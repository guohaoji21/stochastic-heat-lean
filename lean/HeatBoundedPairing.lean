import HeatIntegralBounds

set_option autoImplicit false
noncomputable section
namespace HeatBoundedPairing
open MeasureTheory
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ν : Measure ℝ≥0) [IsFiniteMeasure ν]

theorem integrable (f g : ℝ≥0 → E) (hf : Integrable f ν)
    (hg : AEStronglyMeasurable g ν) (C : ℝ) (hB : ∀ᵐ t ∂ν, ‖g t‖≤C) :
    Integrable (fun t => inner ℝ (f t) (g t)) ν := by
  apply (hf.norm.mul_const C).mono' (hf.aestronglyMeasurable.inner hg)
  filter_upwards [hB] with t ht
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))

end HeatBoundedPairing
#check @HeatBoundedPairing.integrable
#print axioms HeatBoundedPairing.integrable
