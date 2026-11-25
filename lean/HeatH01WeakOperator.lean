import HeatDirichletH01Core
import HeatH01Realization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatH01WeakOperator
open MeasureTheory EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolventForm

def operator : H01 →L[ℝ] H01 := embed.adjoint.comp embed-ContinuousLinearMap.id ℝ H01

theorem pairing (u v : H01) : inner ℝ u (operator v)=
    -inner ℝ (H1Graph.gradL (u : H1Graph volume domain)) (H1Graph.gradL (v : H1Graph volume domain)) := by
  have hi := H1Graph.inner_eq (u : H1Graph volume domain) (v : H1Graph volume domain)
  change inner ℝ u v=inner ℝ (embed u) (embed v)+
    inner ℝ (H1Graph.gradL (u : H1Graph volume domain)) (H1Graph.gradL (v : H1Graph volume domain)) at hi
  change inner ℝ u (embed.adjoint (embed v)-v)=_
  rw [inner_sub_right,embed.adjoint_inner_right]
  linarith

theorem graph_pairing (u : H01) (ψ : Base) (hg : weakLaplacian (embed u) ψ) :
    (innerSL ℝ u).comp operator=(innerSL ℝ ψ).comp embed := by
  obtain ⟨v,hv,hform⟩ := hg
  have hvu : v=u := h01_function_injective hv
  subst v
  apply ContinuousLinearMap.ext
  intro w
  change inner ℝ u (operator w)=inner ℝ ψ (embed w)
  rw [pairing,hform]
  change -(-inner ℝ ψ (embed w))=inner ℝ ψ (embed w)
  exact neg_neg _

theorem adjoint_pairing (u : H01) :
    (innerSL ℝ u).comp embed.adjoint=innerSL ℝ (embed u) := by
  apply ContinuousLinearMap.ext
  intro x
  exact embed.adjoint_inner_right u x

end HeatH01WeakOperator
#check @HeatH01WeakOperator.pairing
#print axioms HeatH01WeakOperator.pairing
#check @HeatH01WeakOperator.graph_pairing
#print axioms HeatH01WeakOperator.graph_pairing
#check @HeatH01WeakOperator.adjoint_pairing
#print HeatH01WeakOperator.adjoint_pairing
#print axioms HeatH01WeakOperator.adjoint_pairing
