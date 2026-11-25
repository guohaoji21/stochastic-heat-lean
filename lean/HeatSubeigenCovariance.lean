import HeatSubeigenEuler
import HeatPaperPositivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatSubeigenCovariance
open MeasureTheory Filter Set HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

variable (C : ℝ) (hC : 0≤C) (f g : Base) (hfg : HeatWeakDirichlet.weakLaplacian f g)
  (hsub : ∀ᵐ x ∂baseMeasure,0 ≤ (g+C • f) x)

include hC hfg hsub in
theorem heat_lower (r : ℝ≥0) :
    ∀ᵐ x ∂baseMeasure,(Real.exp (-C*(r:ℝ)) • f) x≤family r f x := by
  have h := HeatSubeigenEuler.heat_barrier r r.property C hC f g hfg hsub
  filter_upwards [h,Lp.coeFn_sub (paperHeat r f) (Real.exp (-(r:ℝ)*C) • f)] with x hx hs
  rw [hs] at hx
  simpa only [family,neg_mul, mul_comm C (r:ℝ)] using sub_nonneg.mp hx

variable (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
  (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖≤1) (hpos : ∀ᵐ x ∂baseMeasure,0≤b x)
  (hfixed : noise b hb hbound f=f)

include hC hfg hsub hpos hfixed in
theorem integrand_lower (r : ℝ≥0) (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
    ∀ᵐ x ∂baseMeasure,(Real.exp (-C*(r:ℝ)) • f) x≤
      HeatCovarianceOperator.integrand family (noise b hb hbound) r f v x := by
  let s : ℝ≥0 := ⟨v*r,mul_nonneg hv.1 r.property⟩
  let t : ℝ≥0 := ⟨(1-v)*r,mul_nonneg (sub_nonneg.mpr hv.2) r.property⟩
  let a := Real.exp (-C*(s:ℝ))
  let d := Real.exp (-C*(t:ℝ))
  have hs := heat_lower C hC f g hfg hsub s
  have ht := heat_lower C hC f g hfg hsub t
  have h1 := HeatPositiveCone.monotone (noise b hb hbound)
    (HeatPaperPositivity.multiplier_nonnegative b hb hbound hpos) _ _ hs
  rw [map_smul,hfixed] at h1
  have h2 := HeatPositiveCone.monotone (family t) (HeatPaperPositivity.heat_nonnegative t) _ _ h1
  rw [map_smul] at h2
  have had : a*d=Real.exp (-C*(r:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    change -C*(v*(r:ℝ)) + -C*((1-v)*(r:ℝ)) = -C*(r:ℝ)
    ring
  have he : HeatCovarianceOperator.integrand family (noise b hb hbound) r f v=
      family t (noise b hb hbound (family s f)) := by
    have hs' : (v*(r:ℝ)).toNNReal=s := by
      apply NNReal.eq
      exact Real.coe_toNNReal _ (mul_nonneg hv.1 r.property)
    have ht' : ((1-v)*(r:ℝ)).toNNReal=t := by
      apply NNReal.eq
      exact Real.coe_toNNReal _ (mul_nonneg (sub_nonneg.mpr hv.2) r.property)
    change family (((1-v)*(r:ℝ)).toNNReal) (noise b hb hbound (family ((v*(r:ℝ)).toNNReal) f))=_
    rw [hs',ht']
  rw [he]
  filter_upwards [h2,ht,Lp.coeFn_smul a (family t f),Lp.coeFn_smul d f,
    Lp.coeFn_smul (a*d) f] with x h2x htx ha hd hadx
  change (a • family t f) x≤_ at h2x
  change (d • f) x≤family t f x at htx
  rw [ha] at h2x
  rw [hd] at htx
  rw [←had,hadx]
  change d*f x ≤ family t f x at htx
  change a*family t f x ≤ family t (noise b hb hbound (family s f)) x at h2x
  change (a*d)*f x ≤ family t (noise b hb hbound (family s f)) x
  nlinarith [Real.exp_pos (-C*(s:ℝ))]

include hC hfg hsub hpos hfixed in
theorem K_lower (r : ℝ≥0) :
    ∀ᵐ x ∂baseMeasure,(Real.exp (-C*(r:ℝ)) • f) x≤HeatPaperCovariance.K b hb hbound r f x := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν,Real.volume_Ioc]⟩
  let A := HeatCovarianceOperator.integrand family (noise b hb hbound) r f
  let c := Real.exp (-C*(r:ℝ)) • f
  have hInt : Integrable A ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (HeatCovarianceOperator.integrable family family_continuous family_contraction (noise b hb hbound) r f)
  have hnn : ∀ᵐ v ∂ν,∀ᵐ x ∂baseMeasure,0 ≤ (A v-c) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hl := integrand_lower C hC f g hfg hsub b hb hbound hpos hfixed r v ⟨hv.1.le,hv.2⟩
    filter_upwards [hl,Lp.coeFn_sub (A v) c] with x hx hs
    rw [hs]
    exact sub_nonneg.mpr hx
  have h := HeatPositiveCone.integral_nonnegative ν (fun v => A v-c) (hInt.sub (integrable_const c)) hnn
  rw [integral_sub hInt (integrable_const c),integral_const,probReal_univ,one_smul] at h
  have he : (∫ v,A v ∂ν)=HeatPaperCovariance.K b hb hbound r f := by
    change (∫ v,A v ∂ν)=∫ v in (0:ℝ)..1,A v
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rw [he] at h
  filter_upwards [h,Lp.coeFn_sub (HeatPaperCovariance.K b hb hbound r f) c] with x hx hs
  rw [hs] at hx
  exact sub_nonneg.mp hx

end HeatSubeigenCovariance
#check @HeatSubeigenCovariance.K_lower
#print HeatSubeigenCovariance.K_lower
#print axioms HeatSubeigenCovariance.K_lower
