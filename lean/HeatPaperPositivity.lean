import HeatPositiveCone
import HeatDirichletEuler
import HeatPaperCovariance
import HeatBackwardChain

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatPaperPositivity
open MeasureTheory Filter Set HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

theorem heat_nonnegative (r : ℝ≥0) (f : Base) (hf : ∀ᵐ x ∂baseMeasure,0≤f x) :
    ∀ᵐ x ∂baseMeasure,0≤family r f x := HeatDirichletEuler.nonnegative r r.property f hf

variable (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
  (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖≤1) (hpos : ∀ᵐ x ∂baseMeasure,0≤b x)

include hpos in
theorem multiplier_nonnegative (f : Base) (hf : ∀ᵐ x ∂baseMeasure,0≤f x) :
    ∀ᵐ x ∂baseMeasure,0≤noise b hb hbound f x := by
  filter_upwards [hf,hpos,SHEStochastic.BoundedFieldOperator.operator_ae (HeatScalarMultiplier.field baseMeasure b hb hbound) f]
    with x hfx hbx hx
  have he : noise b hb hbound f x=b x*f x := by
    simpa only [noise,HeatScalarMultiplier.field,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul] using hx
  rw [he]
  exact mul_nonneg hbx hfx

include hpos in
theorem K_nonnegative (r : ℝ≥0) (f : Base) (hf : ∀ᵐ x ∂baseMeasure,0≤f x) :
    ∀ᵐ x ∂baseMeasure,0≤HeatPaperCovariance.K b hb hbound r f x := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν,Real.volume_Ioc]⟩
  let A := HeatCovarianceOperator.integrand family (noise b hb hbound) r f
  have hA (v : ℝ) : ∀ᵐ x ∂baseMeasure,0≤A v x :=
    heat_nonnegative _ _ (multiplier_nonnegative b hb hbound hpos _ (heat_nonnegative _ f hf))
  have hInt : Integrable A ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (HeatCovarianceOperator.integrable family family_continuous family_contraction (noise b hb hbound) r f)
  have he := HeatPositiveCone.integral_nonnegative ν A hInt (Eventually.of_forall hA)
  change ∀ᵐ x ∂baseMeasure,0≤(∫ v in (0:ℝ)..1,A v) x
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  exact he

include hpos in
theorem K_monotone (r : ℝ≥0) (f g : Base) (hfg : ∀ᵐ x ∂baseMeasure,f x≤g x) :
    ∀ᵐ x ∂baseMeasure,HeatPaperCovariance.K b hb hbound r f x≤HeatPaperCovariance.K b hb hbound r g x :=
  HeatPositiveCone.monotone _ (K_nonnegative b hb hbound hpos r) f g hfg

include hpos in
theorem chain_nonnegative (h : ℕ → ℝ≥0) (N : ℕ) (g : Base) (hg : ∀ᵐ x ∂baseMeasure,0≤g x) (j : ℕ) :
    ∀ᵐ x ∂baseMeasure,0≤HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g j x := by
  have he (n : ℕ) : ∀ᵐ x ∂baseMeasure,0≤HeatBackwardChain.reverseChain (HeatPaperCovariance.K b hb hbound) h N g n x := by
    induction n with
    | zero => exact hg
    | succ n ih => exact K_nonnegative b hb hbound hpos _ _ ih
  exact he (N-j)

end HeatPaperPositivity
#check @HeatPaperPositivity.heat_nonnegative
#print axioms HeatPaperPositivity.heat_nonnegative
#check @HeatPaperPositivity.multiplier_nonnegative
#print axioms HeatPaperPositivity.multiplier_nonnegative
#check @HeatPaperPositivity.K_nonnegative
#print axioms HeatPaperPositivity.K_nonnegative
#check @HeatPaperPositivity.K_monotone
#print axioms HeatPaperPositivity.K_monotone
#check @HeatPaperPositivity.chain_nonnegative
#print HeatPaperPositivity.chain_nonnegative
#print axioms HeatPaperPositivity.chain_nonnegative
