import HeatScalarMultiplier

set_option autoImplicit false
noncomputable section
namespace HeatMultiplierAdjoint
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem scalar_multiplier_self_adjoint (b : X → ℝ) (hb : AEStronglyMeasurable b μ)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ 1) :
    IsSelfAdjoint (SHEStochastic.BoundedFieldOperator.operator (HeatScalarMultiplier.field μ b hb hbound)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [SHEStochastic.BoundedFieldOperator.operator_ae (HeatScalarMultiplier.field μ b hb hbound) u,
    SHEStochastic.BoundedFieldOperator.operator_ae (HeatScalarMultiplier.field μ b hb hbound) v] with x hu hv
  change SHEStochastic.BoundedFieldOperator.operator (HeatScalarMultiplier.field μ b hb hbound) u x = b x * u x at hu
  change SHEStochastic.BoundedFieldOperator.operator (HeatScalarMultiplier.field μ b hb hbound) v x = b x * v x at hv
  change inner ℝ (SHEStochastic.BoundedFieldOperator.operator (HeatScalarMultiplier.field μ b hb hbound) u x) (v x) =
    inner ℝ (u x) (SHEStochastic.BoundedFieldOperator.operator (HeatScalarMultiplier.field μ b hb hbound) v x)
  rw [hu,hv]
  simp only [real_inner_comm, Real.inner_apply]
  ring

end HeatMultiplierAdjoint
#check @HeatMultiplierAdjoint.scalar_multiplier_self_adjoint
#print axioms HeatMultiplierAdjoint.scalar_multiplier_self_adjoint
