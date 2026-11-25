import HeatDirichletResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatDirichletH01Core
open MeasureTheory EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolventForm

theorem lift_one_eq_adjoint : lift 1 (le_refl 1)=embed.adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro V
  have he := variational (le_refl (1:ℝ)) f V
  have hi := H1Graph.inner_eq (lift 1 (le_refl 1) f : H1Graph volume domain) (V : H1Graph volume domain)
  change inner ℝ (lift 1 (le_refl 1) f) V=inner ℝ (embed (lift 1 (le_refl 1) f)) (embed V)+
    inner ℝ (H1Graph.gradL (lift 1 (le_refl 1) f : H1Graph volume domain))
      (H1Graph.gradL (V : H1Graph volume domain)) at hi
  rw [embed.adjoint_inner_left]
  linarith

theorem lift_one_dense : DenseRange (lift 1 (le_refl 1)) := by
  rw [lift_one_eq_adjoint]
  change Dense (embed.adjoint.range : Set H01)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hk : embed.ker=⊥ := LinearMap.ker_eq_bot.mpr h01_function_injective
  rw [←embed.orthogonal_ker,hk,Submodule.bot_orthogonal_eq_top]

theorem weak_graph_lift_one (f : Base) :
    weakLaplacian (embed (lift 1 (le_refl 1) f)) (embed (lift 1 (le_refl 1) f)-f) := by
  simpa only [HeatDirichletResolvent.resolvent,ContinuousLinearMap.comp_apply,one_smul] using
    HeatDirichletResolvent.weak_graph (le_refl (1:ℝ)) f

end HeatDirichletH01Core
#check @HeatDirichletH01Core.lift_one_eq_adjoint
#print axioms HeatDirichletH01Core.lift_one_eq_adjoint
#check @HeatDirichletH01Core.lift_one_dense
#print axioms HeatDirichletH01Core.lift_one_dense
#check @HeatDirichletH01Core.weak_graph_lift_one
#print HeatDirichletH01Core.weak_graph_lift_one
#print axioms HeatDirichletH01Core.weak_graph_lift_one
