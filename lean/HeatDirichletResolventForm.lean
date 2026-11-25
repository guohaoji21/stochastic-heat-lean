import HeatWeakDirichlet
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatDirichletResolventForm
open MeasureTheory EllipticPdes HeatIntervalNormalization HeatWeakDirichlet
open scoped RealInnerProductSpace

def embed : H01 →L[ℝ] Base := H1Graph.embL2 (volume : Measure ℝ) domain

def operator (a : ℝ) : H01 →L[ℝ] H01 :=
  ContinuousLinearMap.id ℝ H01+(a-1) • (embed.adjoint.comp embed)

def form (a : ℝ) : H01 →L[ℝ] H01 →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ H01).toContinuousLinearEquiv.toContinuousLinearMap.comp (operator a)

theorem form_apply (a : ℝ) (U V : H01) :
    form a U V=a*inner ℝ (embed U) (embed V)+
      inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradL (V : H1Graph volume domain)) := by
  change inner ℝ (operator a U) V=_
  simp only [operator,ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,inner_add_left,real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]
  have hi := H1Graph.inner_eq (U : H1Graph volume domain) (V : H1Graph volume domain)
  change inner ℝ U V=inner ℝ (embed U) (embed V)+
    inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradL (V : H1Graph volume domain)) at hi
  rw [hi]
  ring

theorem coercive {a : ℝ} (ha : 1≤a) : IsCoercive (form a) := by
  refine ⟨1,by norm_num,?_⟩
  intro U
  have hn := H1Graph.norm_sq_eq (U : H1Graph volume domain)
  change ‖U‖^2=‖embed U‖^2+‖H1Graph.gradL (U : H1Graph volume domain)‖^2 at hn
  rw [form_apply,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg ‖embed U‖)]

def lift (a : ℝ) (ha : 1≤a) : Base →L[ℝ] H01 :=
  (coercive ha).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embed.adjoint

theorem variational {a : ℝ} (ha : 1≤a) (f : Base) (V : H01) :
    a*inner ℝ (embed (lift a ha f)) (embed V)+
      inner ℝ (H1Graph.gradL (lift a ha f : H1Graph volume domain))
        (H1Graph.gradL (V : H1Graph volume domain))=inner ℝ f (embed V) := by
  rw [←form_apply]
  calc
    _ = inner ℝ ((coercive ha).continuousLinearEquivOfBilin (lift a ha f)) V :=
      ((coercive ha).continuousLinearEquivOfBilin_apply _ _).symm
    _ = inner ℝ (embed.adjoint f) V := congrArg (fun U : H01 => inner ℝ U V)
      ((coercive ha).continuousLinearEquivOfBilin.apply_symm_apply (embed.adjoint f))
    _ = _ := embed.adjoint_inner_left V f

end HeatDirichletResolventForm
#check @HeatDirichletResolventForm.form_apply
#print axioms HeatDirichletResolventForm.form_apply
#check @HeatDirichletResolventForm.coercive
#print axioms HeatDirichletResolventForm.coercive
#check @HeatDirichletResolventForm.variational
#print HeatDirichletResolventForm.variational
#print axioms HeatDirichletResolventForm.variational
