import HeatSeparatedHeat
import HeatPaperCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4000
noncomputable section
namespace HeatCovarianceSeparation
open MeasureTheory Filter Set HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

variable (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
  (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖≤1)
  (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → b x=0)

include hsupp in
theorem noise_support (f : Base) : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → noise b hb hbound f x=0 := by
  filter_upwards [hsupp,SHEStochastic.BoundedFieldOperator.operator_ae (HeatScalarMultiplier.field baseMeasure b hb hbound) f]
    with x hx hm hxin
  change noise b hb hbound f x=b x*f x at hm
  rw [hm,hx hxin,zero_mul]

theorem noise_contraction (f : Base) : ‖noise b hb hbound f‖≤‖f‖ := by
  simpa only [HeatScalarMultiplier.field,NNReal.coe_one,one_mul] using (noise b hb hbound).le_of_opNorm_le
    (SHEStochastic.BoundedFieldOperator.operator_norm (HeatScalarMultiplier.field baseMeasure b hb hbound)) f

include hsupp in
theorem integrand_bound (r h L : ℝ≥0) (hL : 0<(L:ℝ)) (hrh : r+h≤L) (q : Base)
    (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
    ‖paperBstar (family r (HeatCovarianceOperator.integrand family (noise b hb hbound) h q v))‖≤
      Real.exp (-4/(L:ℝ))*‖q‖ := by
  let s := ((1-v)*(h:ℝ)).toNNReal
  let u := (v*(h:ℝ)).toNNReal
  let f := noise b hb hbound (family u q)
  have hs : (s:ℝ)=(1-v)*(h:ℝ) := Real.coe_toNNReal _ (mul_nonneg (sub_nonneg.mpr hv.2) h.property)
  have hsl : r+s≤L := by
    have hreal : (r:ℝ)+(s:ℝ)≤(L:ℝ) := by
      rw [hs]
      have h0 := mul_nonneg hv.1 h.property
      have hrh' : (r:ℝ)+(h:ℝ)≤(L:ℝ) := by exact_mod_cast hrh
      calc
        _ = (r:ℝ)+(h:ℝ)-v*(h:ℝ) := by ring
        _ ≤ (r:ℝ)+(h:ℝ) := sub_le_self _ h0
        _ ≤ (L:ℝ) := hrh'
    exact_mod_cast hreal
  have he : paperBstar (family r (HeatCovarianceOperator.integrand family (noise b hb hbound) h q v))=
      paperBstar (family (r+s) f) := by
    change paperBstar (family r (family s f))=_
    exact congrArg paperBstar (congrArg (fun A : Base →L[ℝ] Base => A f) (family_semigroup r s)).symm
  rw [he]
  have hd := HeatSeparatedHeat.bound (r+s) L hL hsl f (noise_support b hb hbound hsupp (family u q))
  have hn : ‖f‖≤‖q‖ := (noise_contraction b hb hbound _).trans (family_contraction u q)
  exact hd.trans (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le)

include hsupp in
theorem heat_covariance_bound (r h L : ℝ≥0) (hL : 0<(L:ℝ)) (hrh : r+h≤L) (q : Base) :
    ‖paperBstar (family r (HeatPaperCovariance.K b hb hbound h q))‖≤Real.exp (-4/(L:ℝ))*‖q‖ := by
  let A := HeatCovarianceOperator.integrand family (noise b hb hbound) h q
  let R := paperBstar.comp (family r)
  have hi : IntervalIntegrable A volume 0 1 :=
    HeatCovarianceOperator.integrable family family_continuous family_contraction (noise b hb hbound) h q
  have hcomm := R.intervalIntegral_comp_comm hi
  change ‖R (∫ v in (0:ℝ)..1,A v)‖≤_
  rw [←hcomm]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun v => R (A v))
    (a := (0:ℝ)) (b := 1) (C := Real.exp (-4/(L:ℝ))*‖q‖) (fun v hv => by
      have hv' : v∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using hv
      exact integrand_bound b hb hbound hsupp r h L hL hrh q v ⟨hv'.1.le,hv'.2⟩)
  simpa only [sub_zero,abs_one,mul_one] using hh

include hsupp in
theorem covariance_bound (h L : ℝ≥0) (hL : 0<(L:ℝ)) (hhL : h≤L) (q : Base) :
    ‖paperBstar (HeatPaperCovariance.K b hb hbound h q)‖≤Real.exp (-4/(L:ℝ))*‖q‖ := by
  have he := heat_covariance_bound b hb hbound hsupp 0 h L hL (by simpa only [zero_add] using hhL) q
  simpa only [family,paperHeat_zero,NNReal.coe_zero,ContinuousLinearMap.id_apply] using he

end HeatCovarianceSeparation
#check @HeatCovarianceSeparation.heat_covariance_bound
#print HeatCovarianceSeparation.heat_covariance_bound
#print axioms HeatCovarianceSeparation.heat_covariance_bound
