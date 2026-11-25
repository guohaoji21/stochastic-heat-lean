import HeatIntervalNormalization
import EllipticPdes.Sobolev.GraphDense

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatWeakDirichlet
open MeasureTheory HeatIntervalNormalization EllipticPdes
open scoped NNReal ENNReal RealInnerProductSpace

def domain : Set ℝ := Set.Ioo 0 10
abbrev H01 := H1Graph.H01 (volume : Measure ℝ) domain

/-- The weak Dirichlet Laplacian graph. The zero boundary condition is
encoded as the closure of smooth compactly supported test graphs. -/
def weakLaplacian (f g : Base) : Prop :=
  ∃ U : H01, H1Graph.embL2 (volume : Measure ℝ) domain U = f ∧
    ∀ V : H01, inner ℝ (H1Graph.gradL (U : H1Graph volume domain))
      (H1Graph.gradL (V : H1Graph volume domain)) =
      -inner ℝ g (H1Graph.embL2 (volume : Measure ℝ) domain V)

theorem h01_has_weak_gradient (U : H01) :
    HasWeakFDerivOn ⟨domain, isOpen_Ioo⟩ (H1Graph.fnL (U : H1Graph volume domain))
      (fun x => innerSL ℝ (H1Graph.gradL (U : H1Graph volume domain) x)) volume := by
  apply (H1Graph.mem_W12_iff_hasWeakFDerivOn isOpen_Ioo _).1
  exact H1Graph.H01_le_W12 U.property

theorem weakLaplacian_dissipative (f g : Base) (h : weakLaplacian f g) : inner ℝ g f ≤ 0 := by
  obtain ⟨U, hU, hform⟩ := h
  have he := hform U
  rw [hU, real_inner_self_eq_norm_sq] at he
  nlinarith [sq_nonneg ‖H1Graph.gradL (U : H1Graph volume domain)‖]

theorem boundarySpace_dense : DenseRange (H1Graph.embL2 (volume : Measure ℝ) domain) :=
  H1Graph.denseRange_embL2 isOpen_Ioo


theorem h01_function_injective : Function.Injective (H1Graph.embL2 (volume : Measure ℝ) domain) := by
  intro U V heq
  apply Subtype.ext
  apply H1Graph.ext
  · exact heq
  · have hu := h01_has_weak_gradient U
    have hv := h01_has_weak_gradient V
    have hf : (H1Graph.fnL (U : H1Graph volume domain) : ℝ → ℝ) =ᵐ[volume.restrict domain]
        (H1Graph.fnL (V : H1Graph volume domain) : ℝ → ℝ) := by
      change (H1Graph.embL2 volume domain U : ℝ → ℝ) =ᵐ[volume.restrict domain]
        (H1Graph.embL2 volume domain V : ℝ → ℝ)
      rw [heq]
    have hu' := hu.congr_ae hf Filter.EventuallyEq.rfl
    have hgrad := hu'.ae_eq hv
    apply Lp.ext
    filter_upwards [hgrad] with x hx
    have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hx
    simpa [real_inner_comm, Real.inner_apply] using he

theorem weakLaplacian_symmetric (f g p q : Base)
    (hfg : weakLaplacian f g) (hpq : weakLaplacian p q) :
    inner ℝ g p = inner ℝ f q := by
  obtain ⟨U, hU, hformU⟩ := hfg
  obtain ⟨V, hV, hformV⟩ := hpq
  have h1 := hformU V
  have h2 := hformV U
  rw [hV] at h1
  rw [hU] at h2
  have hc := real_inner_comm (H1Graph.gradL (U : H1Graph volume domain))
    (H1Graph.gradL (V : H1Graph volume domain))
  have hf := real_inner_comm f q
  linarith


theorem weakLaplacian_unique (f g h : Base)
    (hfg : weakLaplacian f g) (hfh : weakLaplacian f h) : g = h := by
  obtain ⟨U, hU, hformU⟩ := hfg
  obtain ⟨V, hV, hformV⟩ := hfh
  have hUV : U = V := h01_function_injective (hU.trans hV.symm)
  subst V
  have htest : ∀ W : H01, inner ℝ g (H1Graph.embL2 volume domain W) =
      inner ℝ h (H1Graph.embL2 volume domain W) := by
    intro W
    have hu := hformU W
    have hv := hformV W
    linarith
  apply ext_inner_right ℝ
  intro z
  refine boundarySpace_dense.induction_on (p := fun z : Base => inner ℝ g z = inner ℝ h z) z ?_ ?_
  · exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  · exact htest


/-- The resolvent equation u - Δu = f has a weak zero-boundary solution. -/
theorem weakLaplacian_resolvent_surjective (f : Base) :
    ∃ u g : Base, weakLaplacian u g ∧ u - g = f := by
  let L : H01 →L[ℝ] ℝ := (innerSL ℝ f).comp (H1Graph.embL2 volume domain)
  let U : H01 := (InnerProductSpace.toDual ℝ H01).symm L
  have hU : ∀ V : H01, inner ℝ U V = inner ℝ f (H1Graph.embL2 volume domain V) := by
    intro V
    have he := congrArg (fun A : H01 →L[ℝ] ℝ => A V)
      ((InnerProductSpace.toDual ℝ H01).apply_symm_apply L)
    change inner ℝ U V = inner ℝ f (H1Graph.embL2 volume domain V) at he
    exact he
  let u : Base := H1Graph.embL2 volume domain U
  let g : Base := u-f
  refine ⟨u, g, ?_, ?_⟩
  · refine ⟨U, rfl, ?_⟩
    intro V
    have he := hU V
    have hs : inner ℝ U V = inner ℝ u (H1Graph.embL2 volume domain V) +
        inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradL (V : H1Graph volume domain)) :=
      H1Graph.inner_eq (U : H1Graph volume domain) (V : H1Graph volume domain)
    change inner ℝ (H1Graph.gradL (U : H1Graph volume domain))
      (H1Graph.gradL (V : H1Graph volume domain)) =
      -inner ℝ (u-f) (H1Graph.embL2 volume domain V)
    simp only [inner_sub_left] 
    linarith
  · dsimp [g]
    exact sub_sub_cancel _ _


/-- A dissipative graph extending the weak Laplacian cannot add new pairs.
This is an abstract comparison criterion, not yet the semigroup identification. -/
theorem weakLaplacian_no_dissipative_extension
    (candidate : Base → Base → Prop)
    (hext : ∀ f g, weakLaplacian f g → candidate f g)
    (hdiss : ∀ f g u v, candidate f g → candidate u v →
      inner ℝ (g-v) (f-u) ≤ 0)
    (f g : Base) (hfg : candidate f g) : weakLaplacian f g := by
  obtain ⟨u,v,hweak,hres⟩ := weakLaplacian_resolvent_surjective (f-g)
  have hd := hdiss f g u v hfg (hext u v hweak)
  have he : f-u = g-v := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa [add_comm] using (sub_eq_sub_iff_add_eq_add.mp hres).symm
  rw [← he, real_inner_self_eq_norm_sq] at hd
  have hz : f-u = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (f-u)])
  have hf : f = u := sub_eq_zero.mp hz
  have hg : g = v := by rw [hf, sub_self] at he; exact (sub_eq_zero.mp he.symm)
  simpa only [hf, hg] using hweak

end HeatWeakDirichlet
#check @HeatWeakDirichlet.h01_has_weak_gradient
#print axioms HeatWeakDirichlet.h01_has_weak_gradient
#check @HeatWeakDirichlet.weakLaplacian_dissipative
#print axioms HeatWeakDirichlet.weakLaplacian_dissipative
#check @HeatWeakDirichlet.boundarySpace_dense
#print axioms HeatWeakDirichlet.boundarySpace_dense

#check @HeatWeakDirichlet.h01_function_injective
#print axioms HeatWeakDirichlet.h01_function_injective
#check @HeatWeakDirichlet.weakLaplacian_symmetric
#print axioms HeatWeakDirichlet.weakLaplacian_symmetric

#check @HeatWeakDirichlet.weakLaplacian_unique
#print axioms HeatWeakDirichlet.weakLaplacian_unique

#check @HeatWeakDirichlet.weakLaplacian_resolvent_surjective
#print axioms HeatWeakDirichlet.weakLaplacian_resolvent_surjective

#check @HeatWeakDirichlet.weakLaplacian_no_dissipative_extension
#print axioms HeatWeakDirichlet.weakLaplacian_no_dissipative_extension
