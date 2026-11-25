import HeatDeterministicPairing

set_option autoImplicit false
noncomputable section
namespace HeatIntegralBounds
open MeasureTheory Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (ν : Measure ℝ≥0) [IsFiniteMeasure ν]

theorem cumulative_bound (f : ℝ≥0 → E) (hf : Integrable f ν) (t : ℝ≥0) :
    ‖∫ s in Iio t, f s ∂ν‖≤∫ s,‖f s‖ ∂ν := by
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun s => norm_nonneg (f s))) hf.norm)

end HeatIntegralBounds
#check @HeatIntegralBounds.cumulative_bound
#print axioms HeatIntegralBounds.cumulative_bound
