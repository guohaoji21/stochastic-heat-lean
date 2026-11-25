import HeatCanonicalHeatMoments
import HeatCovarianceAdjoint
import HeatMultiplierAdjoint

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatPaperCovariance
open MeasureTheory HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal

local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure; infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

def K (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (r : ℝ≥0) : Base →L[ℝ] Base :=
  HeatCovarianceOperator.covariance family family_continuous family_contraction (noise b hb hbound) r

theorem K_norm (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (r : ℝ≥0) : ‖K b hb hbound r‖ ≤ 1 :=
  (HeatCovarianceOperator.covariance_norm family family_continuous family_contraction (noise b hb hbound) r).trans
    (SHEStochastic.BoundedFieldOperator.operator_norm (HeatScalarMultiplier.field baseMeasure b hb hbound))

theorem K_contraction (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (r : ℝ≥0) (q : Base) : ‖K b hb hbound r q‖ ≤ ‖q‖ := by
  simpa only [one_mul] using (K b hb hbound r).le_of_opNorm_le (K_norm b hb hbound r) q

theorem K_continuous (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (q : Base) : Continuous (fun r => K b hb hbound r q) :=
  HeatCovarianceOperator.covariance_continuous family family_continuous family_contraction (noise b hb hbound) q

theorem K_self_adjoint (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (r : ℝ≥0) : (K b hb hbound r).adjoint = K b hb hbound r := by
  apply HeatCovarianceAdjoint.covariance_self_adjoint family family_continuous family_contraction (noise b hb hbound)
  · intro t x y
    exact HeatPaperAdjoint.paper_heat_inner t x y
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (HeatMultiplierAdjoint.scalar_multiplier_self_adjoint baseMeasure b hb hbound)

theorem K_zero (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (q : Base) : K b hb hbound 0 q = noise b hb hbound q :=
  HeatCovarianceOperator.covariance_zero family family_continuous family_contraction (noise b hb hbound) paperHeat_zero q

end HeatPaperCovariance
#check @HeatPaperCovariance.K_norm
#print axioms HeatPaperCovariance.K_norm
#check @HeatPaperCovariance.K_contraction
#print axioms HeatPaperCovariance.K_contraction
#check @HeatPaperCovariance.K_continuous
#print axioms HeatPaperCovariance.K_continuous
#check @HeatPaperCovariance.K_self_adjoint
#print axioms HeatPaperCovariance.K_self_adjoint
#check @HeatPaperCovariance.K_zero
#print axioms HeatPaperCovariance.K_zero
