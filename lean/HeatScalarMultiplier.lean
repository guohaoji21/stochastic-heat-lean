import SHEStochastic.BoundedFieldOperator

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped NNReal
namespace HeatScalarMultiplier

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def field (b : X → ℝ) (hb : AEStronglyMeasurable b μ)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ 1) : SHEStochastic.BoundedFieldOperator.Field μ ℝ ℝ where
  value x := b x • ContinuousLinearMap.id ℝ ℝ
  measurable := hb.smul aestronglyMeasurable_const
  bound := 1
  norm_bound := by
    filter_upwards [hbound] with x hx
    calc
      ‖b x • ContinuousLinearMap.id ℝ ℝ‖ = ‖b x‖ * ‖ContinuousLinearMap.id ℝ ℝ‖ := norm_smul _ _
      _ ≤ ‖b x‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ ≤ 1 := by simpa using hx

theorem exists_multiplier (b : X → ℝ) (hb : AEStronglyMeasurable b μ)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ 1) :
    ∃ M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      ‖M‖ ≤ 1 ∧ ∀ y : Lp ℝ 2 μ, (fun x => M y x) =ᵐ[μ] fun x => b x * y x := by
  let A := field μ b hb hbound
  refine ⟨SHEStochastic.BoundedFieldOperator.operator A, ?_, ?_⟩
  · exact SHEStochastic.BoundedFieldOperator.operator_norm A
  · intro y
    filter_upwards [SHEStochastic.BoundedFieldOperator.operator_ae A y] with x hx
    simpa [A, field, smul_eq_mul] using hx

end HeatScalarMultiplier
#check @HeatScalarMultiplier.exists_multiplier
#print axioms HeatScalarMultiplier.exists_multiplier
