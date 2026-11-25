import HeatDirichletResolventForm
import HeatWeakDirichletAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatDirichletResolvent
open MeasureTheory EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolventForm

def resolvent (a : ℝ) (ha : 1≤a) : Base →L[ℝ] Base := embed.comp (lift a ha)
def smoothing (a : ℝ) (ha : 1≤a) : Base →L[ℝ] Base := a • resolvent a ha

theorem weak_graph {a : ℝ} (ha : 1≤a) (f : Base) :
    weakLaplacian (resolvent a ha f) (a • resolvent a ha f-f) := by
  refine ⟨lift a ha f,rfl,?_⟩
  intro V
  have hv := variational ha f V
  change _ = -inner ℝ (a • embed (lift a ha f)-f) (embed V)
  simp only [inner_sub_left,real_inner_smul_left]
  linarith

theorem norm_bound {a : ℝ} (ha : 1≤a) (f : Base) : ‖resolvent a ha f‖≤‖f‖/a := by
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have he := variational ha f (lift a ha f)
  change a*inner ℝ (resolvent a ha f) (resolvent a ha f)+
    inner ℝ (H1Graph.gradL (lift a ha f : H1Graph volume domain))
      (H1Graph.gradL (lift a ha f : H1Graph volume domain))=inner ℝ f (resolvent a ha f) at he
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
  have hh := real_inner_le_norm f (resolvent a ha f)
  by_cases hz : ‖resolvent a ha f‖=0
  · rw [hz]
    exact div_nonneg (norm_nonneg _) ha0.le
  · have hp : 0<‖resolvent a ha f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (le_div_iff₀ ha0).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [sq_nonneg ‖H1Graph.gradL (lift a ha f : H1Graph volume domain)‖]

theorem symmetric {a : ℝ} (ha : 1≤a) (f g : Base) :
    inner ℝ (resolvent a ha f) g=inner ℝ f (resolvent a ha g) := by
  have hfg := variational ha f (lift a ha g)
  have hgf := variational ha g (lift a ha f)
  have hinner : inner ℝ (embed (lift a ha g)) (embed (lift a ha f))=
      inner ℝ (embed (lift a ha f)) (embed (lift a ha g)) := real_inner_comm _ _
  have hgrad : inner ℝ (H1Graph.gradL (lift a ha g : H1Graph volume domain))
      (H1Graph.gradL (lift a ha f : H1Graph volume domain))=
      inner ℝ (H1Graph.gradL (lift a ha f : H1Graph volume domain))
        (H1Graph.gradL (lift a ha g : H1Graph volume domain)) := real_inner_comm _ _
  rw [hinner,hgrad] at hgf
  change inner ℝ (embed (lift a ha f)) g=inner ℝ f (embed (lift a ha g))
  calc
    _ = inner ℝ g (embed (lift a ha f)) := real_inner_comm _ _
    _ = _ := by linarith

theorem smoothing_contraction {a : ℝ} (ha : 1≤a) (f : Base) : ‖smoothing a ha f‖≤‖f‖ := by
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  change ‖a • resolvent a ha f‖≤_
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
  exact (mul_le_mul_of_nonneg_left (norm_bound ha f) ha0.le).trans_eq
    (by field_simp)

theorem smoothing_symmetric {a : ℝ} (ha : 1≤a) (f g : Base) :
    inner ℝ (smoothing a ha f) g=inner ℝ f (smoothing a ha g) := by
  change inner ℝ (a • resolvent a ha f) g=inner ℝ f (a • resolvent a ha g)
  rw [real_inner_smul_left,real_inner_smul_right,symmetric ha]

theorem smoothing_graph {a : ℝ} (ha : 1≤a) (f : Base) :
    weakLaplacian (smoothing a ha f) (a • (smoothing a ha f-f)) :=
  HeatWeakDirichletAlgebra.smul a _ _ (weak_graph ha f)

end HeatDirichletResolvent
#check @HeatDirichletResolvent.weak_graph
#print axioms HeatDirichletResolvent.weak_graph
#check @HeatDirichletResolvent.norm_bound
#print axioms HeatDirichletResolvent.norm_bound
#check @HeatDirichletResolvent.symmetric
#print axioms HeatDirichletResolvent.symmetric
#check @HeatDirichletResolvent.smoothing_contraction
#print axioms HeatDirichletResolvent.smoothing_contraction
#check @HeatDirichletResolvent.smoothing_symmetric
#print axioms HeatDirichletResolvent.smoothing_symmetric
#check @HeatDirichletResolvent.smoothing_graph
#print HeatDirichletResolvent.smoothing_graph
#print axioms HeatDirichletResolvent.smoothing_graph
