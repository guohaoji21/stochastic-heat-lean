import HeatWeightedSobolev
import HeatDirichletResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatWeightedResolvent
open MeasureTheory Filter EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolventForm
open HeatExponentialWeight

theorem energy {a α : ℝ} (ha : 1≤a) (f : Base) :
    let U := lift a ha f
    a*‖weight α (embed U)‖^2+‖weight α (H1Graph.gradL (U : H1Graph volume domain))‖^2+
      2*α*inner ℝ (weight α (H1Graph.gradL (U : H1Graph volume domain))) (weight α (embed U))=
      inner ℝ (weight α f) (weight α (embed U)) := by
  let U := lift a ha f
  let V := HeatWeightedSobolev.map (2*α) U
  have he := variational ha f V
  have hfn : embed V=weight (2*α) (embed U) := rfl
  have hgrad : H1Graph.gradL (V : H1Graph volume domain)=
      weight (2*α) (H1Graph.gradL (U : H1Graph volume domain))+
        (2*α) • weight (2*α) (embed U) := rfl
  change a*inner ℝ (embed U) (embed V)+inner ℝ (H1Graph.gradL (U : H1Graph volume domain))
    (H1Graph.gradL (V : H1Graph volume domain))=inner ℝ f (embed V) at he
  rw [hfn,hgrad,inner_add_right,real_inner_smul_right] at he
  let u : Base := embed U
  let v : Base := H1Graph.gradL (U : H1Graph volume domain)
  change a*inner ℝ u (weight (2*α) u)+(inner ℝ v (weight (2*α) v)+
    2*α*inner ℝ v (weight (2*α) u))=inner ℝ f (weight (2*α) u) at he
  have h1 := inner_identity α u u
  have h2 := inner_identity α v v
  have h3 := inner_identity α v u
  have h4 := inner_identity α f u
  rw [real_inner_self_eq_norm_sq] at h1 h2
  change a*‖weight α u‖^2+‖weight α v‖^2+2*α*inner ℝ (weight α v) (weight α u)=inner ℝ (weight α f) (weight α u)
  rw [h1,h2,h3,h4]
  linarith

theorem bound {a α : ℝ} (ha : 1≤a) (hα : α^2<a) (f : Base) :
    ‖weight α (HeatDirichletResolvent.resolvent a ha f)‖≤‖weight α f‖/(a-α^2) := by
  let U := lift a ha f
  let x := weight α (embed U)
  let y := weight α (H1Graph.gradL (U : H1Graph volume domain))
  have he := energy (α := α) ha f
  change a*‖x‖^2+‖y‖^2+2*α*inner ℝ y x=inner ℝ (weight α f) x at he
  have hnon : 0 ≤ inner ℝ (y+α • x) (y+α • x) := real_inner_self_nonneg
  simp only [inner_add_left,inner_add_right,real_inner_smul_right,real_inner_smul_left,
    real_inner_self_eq_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] at hnon
  have hcomm : inner ℝ x y=inner ℝ y x := real_inner_comm y x
  rw [hcomm] at hnon
  have hc := real_inner_le_norm (weight α f) x
  have hβ : 0<a-α^2 := sub_pos.mpr hα
  change ‖x‖≤‖weight α f‖/(a-α^2)
  apply (le_div_iff₀ hβ).mpr
  by_cases hx : x=0
  · simp [hx]
  · have hxp : 0<‖x‖ := norm_pos_iff.mpr hx
    apply (mul_le_mul_iff_right₀ hxp).mp
    have hb : (a-α^2)*‖x‖^2≤‖weight α f‖*‖x‖ := by nlinarith
    convert hb using 1 <;> ring

end HeatWeightedResolvent
#check @HeatWeightedResolvent.bound
#print HeatWeightedResolvent.bound
#print axioms HeatWeightedResolvent.bound
