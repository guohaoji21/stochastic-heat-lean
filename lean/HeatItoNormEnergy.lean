import HeatItoProduct
import HeatTimeRestriction

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatItoNormEnergy
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem energy (hl : StandardTerminalPastLocality I)
    (x₀ : Lp E 2 μ) (hx₀ : AEStronglyMeasurable[F 0] x₀ μ)
    (f : ℝ≥0 → Lp E 2 μ) (hf : Integrable f (timeMeasure H))
    (ha : ∀ᵐ t ∂timeMeasure H, AEStronglyMeasurable[F t] (f t) μ)
    (h : Process (E := E) F μ H) (V : ℝ≥0 → Lp E 2 μ)
    (hrep : ∀ t, t≤H → V t=x₀+HeatDeterministicPairing.cumulative (timeMeasure H) f t+
      HeatStoppedPairing.value F μ H I h t) :
    ‖V H‖^2-‖x₀‖^2=2*(∫ t,inner ℝ (f t) (V t) ∂timeMeasure H)+
      ‖StoppedItoInputs.stop F μ H H h‖^2 := by
  let X := fun t => x₀+HeatDeterministicPairing.cumulative (timeMeasure H) f t+HeatStoppedPairing.value F μ H I h t
  have hX (t : ℝ≥0) (ht : t≤H) : X t=V t := (hrep t ht).symm
  have hEnd : x₀+(∫ t,f t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I h H=V H := by
    have hh := hX H le_rfl
    dsimp only [X,HeatDeterministicPairing.cumulative] at hh
    rw [HeatTimeRestriction.restrict_Iio le_rfl] at hh
    exact hh
  have hp := HeatItoProduct.product_rule F μ H I hl x₀ x₀ hx₀ hx₀ f f hf hf ha ha h h
  change inner ℝ (x₀+(∫ t,f t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I h H)
      (x₀+(∫ t,f t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I h H)-inner ℝ x₀ x₀=
    (∫ t,inner ℝ (f t) (X t) ∂timeMeasure H)+(∫ t,inner ℝ (X t) (f t) ∂timeMeasure H)+
      inner ℝ (StoppedItoInputs.stop F μ H H h) (StoppedItoInputs.stop F μ H H h) at hp
  rw [hEnd,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hp
  have hleft : (fun t => inner ℝ (f t) (X t))=ᵐ[timeMeasure H] fun t => inner ℝ (f t) (V t) := by
    filter_upwards [timeMeasure_ae_mem H] with t ht
    rw [hX t ht.2]
  have hright : (fun t => inner ℝ (X t) (f t))=ᵐ[timeMeasure H] fun t => inner ℝ (f t) (V t) := by
    filter_upwards [timeMeasure_ae_mem H] with t ht
    rw [hX t ht.2]
    exact real_inner_comm _ _
  rw [integral_congr_ae hleft,integral_congr_ae hright] at hp
  linarith

end HeatItoNormEnergy
#check @HeatItoNormEnergy.energy
#print HeatItoNormEnergy.energy
#print axioms HeatItoNormEnergy.energy
