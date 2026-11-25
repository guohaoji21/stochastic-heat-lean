import HeatControlConvolution
import HeatControlAdapted

set_option autoImplicit false
noncomputable section
namespace HeatClampedControl
open MeasureTheory Filter SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (U : ℝ≥0 → Ω → E) (hU : IsStronglyProgressive F U)

include hU in
theorem square_integrable (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    MemLp (HeatControlAdapted.clamp U H) 2 (energyMeasure μ H) := by
  have hm := HeatControlAdapted.clamp_measurable F U hU H
  have he : HeatControlAdapted.clamp U H=ᵐ[energyMeasure μ H] Function.uncurry U := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    simp only [HeatControlAdapted.clamp,min_eq_left hp.2,Function.uncurry_apply_pair]
    rfl
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact hE.congr (he.fun_comp (fun z : E => ‖z‖^2)).symm

end HeatClampedControl
#check @HeatClampedControl.square_integrable
#print HeatClampedControl.square_integrable
#print axioms HeatClampedControl.square_integrable
