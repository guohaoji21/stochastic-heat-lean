import HeatMildKernelCross
import HeatTerminalNaturality

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatRegularizedKernelCross
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)

theorem cross (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    {a b : ℝ≥0} (hab : a≤b) (ρ : ℝ≥0) (u v : Process (E := E) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    inner ℝ (((S ρ).compLpL 2 ν) (HeatMildKernelCross.forward F μ H S hS hcontr M a b u))
      (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v)=
      ∫ p, (Ioc a b).indicator (fun s => inner ℝ (M (u (s,p.2))) (S (ρ+(b-a)) (v (s,p.2)))) p.1 ∂energyMeasure μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let U := HeatMildKernelCross.forward F μ H S hS hcontr M a b u
  let V := HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v
  let CU := ((S ρ).compLpL 2 ν) U
  have hmap := ae_eq_of_ae_eq_trim ((S ρ).coeFn_compLpL U)
  have hm : StronglyMeasurable[F.predictable] (fun p => inner ℝ (CU p) (V p)) :=
    (Lp.stronglyMeasurable CU).inner (Lp.stronglyMeasurable V)
  rw [L2.inner_def,←integral_trim (predictable_le_product F) hm]
  apply integral_congr_ae
  filter_upwards [hmap,HeatMildKernelCross.forward_ae F μ H S hS hcontr M a b u,
    HeatBackwardKernel.input_ae F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v] with p hm hu hv
  change inner ℝ (CU p) (V p)=_
  change CU p=S ρ (U p) at hm
  rw [hm]
  change inner ℝ (S ρ (HeatMildKernelCross.forward F μ H S hS hcontr M a b u p))
    (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v p)=_
  rw [hu,hv]
  by_cases hp : p.1∈Ioc a b
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,Set.indicator_of_mem hp]
    simp only [ContinuousLinearMap.id_apply]
    rw [hsym ρ,hsym (b-p.1)]
    have h1 := congrArg (fun A : E →L[ℝ] E => A (v p)) (hsem ρ (p.1-a))
    change S (ρ+(p.1-a)) (v p)=S ρ (S (p.1-a) (v p)) at h1
    rw [←h1]
    have h2 := congrArg (fun A : E →L[ℝ] E => A (v p)) (hsem (b-p.1) (ρ+(p.1-a)))
    have ht : b-p.1+(ρ+(p.1-a))=ρ+(b-a) := by
      calc
        _ = ρ+(b-p.1+(p.1-a)) := by ac_rfl
        _ = _ := congrArg (fun r => ρ+r) (tsub_add_tsub_cancel hp.2 hp.1.le)
    rw [ht] at h2
    exact congrArg (fun z => inner ℝ (M (u p)) z) h2.symm
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,map_zero]
    simp

variable {κ : Type*} [Countable κ] (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem ito_cross (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    {a b : ℝ≥0} (hab : a≤b) (ρ : ℝ≥0) (u v : Process (E := E) F μ H) :
    inner ℝ (((S ρ).compLpL 2 μ) ((I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u)))
      ((I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v))=
      ∫ p, (Ioc a b).indicator (fun s => inner ℝ (M (u (s,p.2))) (S (ρ+(b-a)) (v (s,p.2)))) p.1 ∂energyMeasure μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [HeatTerminalNaturality.commutes]
  exact ((I).integral.inner_map_map _ _).trans
    (cross F μ H S hS hcontr M hsem hsym hab ρ u v)

end HeatRegularizedKernelCross
#check @HeatRegularizedKernelCross.cross
#print HeatRegularizedKernelCross.cross
#print axioms HeatRegularizedKernelCross.cross

#check @HeatRegularizedKernelCross.ito_cross
#print HeatRegularizedKernelCross.ito_cross
#print axioms HeatRegularizedKernelCross.ito_cross
