import HeatWeakDirichlet
import SHEStochastic.BoundedFieldOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatExponentialWeight
open MeasureTheory Filter EllipticPdes HeatIntervalNormalization HeatWeakDirichlet
open scoped NNReal ENNReal

def value (a x : ℝ) : ℝ := Real.exp (a*x)

theorem bound (a : ℝ) : ∀ᵐ x ∂baseMeasure,‖value a x‖≤Real.exp (10*|a|) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change ‖Real.exp (a*x)‖≤Real.exp (10*|a|)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self a) hx.1.le
  have h2 := mul_le_mul_of_nonneg_left hx.2.le (abs_nonneg a)
  nlinarith

def field (a : ℝ) : SHEStochastic.BoundedFieldOperator.Field baseMeasure ℝ ℝ where
  value x := value a x • ContinuousLinearMap.id ℝ ℝ
  measurable := (by unfold value;fun_prop : AEStronglyMeasurable (value a) baseMeasure).smul aestronglyMeasurable_const
  bound := ⟨Real.exp (10*|a|),(Real.exp_pos _).le⟩
  norm_bound := by
    filter_upwards [bound a] with x hx
    calc
      ‖value a x • ContinuousLinearMap.id ℝ ℝ‖ = ‖value a x‖*‖ContinuousLinearMap.id ℝ ℝ‖ := norm_smul _ _
      _ ≤ ‖value a x‖*1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ ≤ Real.exp (10*|a|) := by simpa only [mul_one] using hx

def weight (a : ℝ) : Base →L[ℝ] Base := SHEStochastic.BoundedFieldOperator.operator (field a)

theorem weight_ae (a : ℝ) (f : Base) :
    (weight a f : ℝ → ℝ)=ᵐ[baseMeasure] fun x => value a x*f x := by
  filter_upwards [SHEStochastic.BoundedFieldOperator.operator_ae (field a) f] with x hx
  simpa only [weight,field,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul] using hx

theorem weight_comp (a b : ℝ) (f : Base) : weight a (weight b f)=weight (a+b) f := by
  apply Lp.ext
  filter_upwards [weight_ae a (weight b f),weight_ae b f,weight_ae (a+b) f] with x ha hb hab
  rw [ha,hb,hab]
  simp only [value,add_mul,Real.exp_add]
  ring

theorem weight_zero (f : Base) : weight 0 f=f := by
  apply Lp.ext
  filter_upwards [weight_ae 0 f] with x hx
  simpa only [value,zero_mul,Real.exp_zero,one_mul] using hx

theorem inner_identity (a : ℝ) (f g : Base) :
    inner ℝ (weight a f) (weight a g)=inner ℝ f (weight (2*a) g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weight_ae a f,weight_ae a g,weight_ae (2*a) g] with x hf hg h2
  simp only [Real.inner_apply]
  rw [hf,hg,h2]
  have he : value (2*a) x=value a x*value a x := by unfold value;rw [←Real.exp_add];congr 1;ring
  rw [he]
  ring

end HeatExponentialWeight
#check @HeatExponentialWeight.inner_identity
#print HeatExponentialWeight.inner_identity
#print axioms HeatExponentialWeight.inner_identity
