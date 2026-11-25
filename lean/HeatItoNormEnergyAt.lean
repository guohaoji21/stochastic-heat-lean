import HeatItoNormEnergy
import HeatItoStopAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatItoNormEnergyAt
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem energy (hl : StandardTerminalPastLocality I)
    (x₀ : Lp E 2 μ) (hx₀ : AEStronglyMeasurable[F 0] x₀ μ)
    (f : ℝ≥0 → Lp E 2 μ) (hf : Integrable f (timeMeasure H))
    (ha : ∀ᵐ t ∂timeMeasure H,AEStronglyMeasurable[F t] (f t) μ)
    (h : Process (E := E) F μ H) (V : ℝ≥0 → Lp E 2 μ)
    (hrep : ∀ t,t ≤ H → V t=x₀+HeatDeterministicPairing.cumulative (timeMeasure H) f t+
      HeatStoppedPairing.value F μ H I h t) {T : ℝ≥0} (hT : T ≤ H) :
    ‖V T‖^2-‖x₀‖^2=2*(∫ t,inner ℝ (f t) (V t) ∂timeMeasure T)+
      ‖StoppedItoInputs.stop F μ H T h‖^2 := by
  let fD := (Iio T).indicator f
  let hD := StoppedItoInputs.stop F μ H T h
  have hfD : Integrable fD (timeMeasure H) := hf.indicator measurableSet_Iio
  have haD : ∀ᵐ t ∂timeMeasure H,AEStronglyMeasurable[F t] (fD t) μ := by
    filter_upwards [ha] with t ht
    by_cases hs : t<T
    · have he : fD t=f t := Set.indicator_of_mem (show t∈Iio T from hs) f
      rw [he]
      exact ht
    · have he : fD t=0 := Set.indicator_of_notMem (show t∉Iio T from hs) f
      rw [he]
      exact stronglyMeasurable_const.aestronglyMeasurable.congr (Lp.coeFn_zero E 2 μ).symm
  let X := fun t => x₀+HeatDeterministicPairing.cumulative (timeMeasure H) fD t+
    HeatStoppedPairing.value F μ H I hD t
  have hXs (s : ℝ≥0) (hs : s ≤ T) : X s=V s := by
    dsimp only [X,fD,hD,HeatStoppedPairing.value]
    rw [HeatItoStopAlgebra.cumulative_indicator,HeatItoStopAlgebra.stop_min,min_eq_left hs]
    exact (hrep s (hs.trans hT)).symm
  have hEnd : x₀+(∫ t,fD t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I hD H=V T := by
    dsimp only [fD,hD,HeatStoppedPairing.value]
    rw [integral_indicator measurableSet_Iio,HeatItoStopAlgebra.stop_min,min_eq_right hT]
    exact (hrep T hT).symm
  have hp := HeatItoProduct.product_rule F μ H I hl x₀ x₀ hx₀ hx₀ fD fD hfD hfD haD haD hD hD
  change inner ℝ (x₀+(∫ t,fD t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I hD H)
      (x₀+(∫ t,fD t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I hD H)-inner ℝ x₀ x₀=
    (∫ t,inner ℝ (fD t) (X t) ∂timeMeasure H)+(∫ t,inner ℝ (X t) (fD t) ∂timeMeasure H)+
      inner ℝ (StoppedItoInputs.stop F μ H H hD) (StoppedItoInputs.stop F μ H H hD) at hp
  rw [hEnd,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hp
  have he1 : (fun t => inner ℝ (fD t) (X t))=(Iio T).indicator (fun t => inner ℝ (f t) (V t)) := by
    funext t
    by_cases ht : t<T
    · have hfT : fD t=f t := Set.indicator_of_mem (show t∈Iio T from ht) f
      have hi : ((Iio T).indicator (fun u => inner ℝ (f u) (V u))) t=inner ℝ (f t) (V t) :=
        Set.indicator_of_mem (show t∈Iio T from ht) _
      rw [hfT,hi,hXs t ht.le]
    · have hfT : fD t=0 := Set.indicator_of_notMem (show t∉Iio T from ht) f
      have hi : ((Iio T).indicator (fun u => inner ℝ (f u) (V u))) t=0 :=
        Set.indicator_of_notMem (show t∉Iio T from ht) _
      rw [hfT,hi,inner_zero_left]
  have he2 : (fun t => inner ℝ (X t) (fD t))=(Iio T).indicator (fun t => inner ℝ (f t) (V t)) := by
    funext t
    by_cases ht : t<T
    · have hfT : fD t=f t := Set.indicator_of_mem (show t∈Iio T from ht) f
      have hi : ((Iio T).indicator (fun u => inner ℝ (f u) (V u))) t=inner ℝ (f t) (V t) :=
        Set.indicator_of_mem (show t∈Iio T from ht) _
      rw [hfT,hi,hXs t ht.le]
      exact real_inner_comm _ _
    · have hfT : fD t=0 := Set.indicator_of_notMem (show t∉Iio T from ht) f
      have hi : ((Iio T).indicator (fun u => inner ℝ (f u) (V u))) t=0 :=
        Set.indicator_of_notMem (show t∉Iio T from ht) _
      rw [hfT,hi,inner_zero_right]
  rw [he1,he2,integral_indicator measurableSet_Iio,HeatTimeRestriction.restrict_Iio hT] at hp
  have hn : StoppedItoInputs.stop F μ H H hD=StoppedItoInputs.stop F μ H T h := by
    exact (HeatItoStopAlgebra.stop_min F μ H H T h).trans (congrArg (fun s : ℝ≥0 => StoppedItoInputs.stop F μ H s h) (min_eq_right hT))
  rw [hn] at hp
  linarith

end HeatItoNormEnergyAt
#check @HeatItoNormEnergyAt.energy
#print axioms HeatItoNormEnergyAt.energy
