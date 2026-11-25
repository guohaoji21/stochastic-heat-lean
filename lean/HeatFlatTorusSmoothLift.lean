import HeatTorusGevreyCutoff
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatFlatTorusSmoothLift

open Topology

variable {ι : Type*} [Fintype ι]

/-- The covering in physical Euclidean coordinates. -/
def covering (P : ℝ) : EuclideanSpace ℝ ι →+ (ι → AddCircle P) where
  toFun x i := (x i : AddCircle P)
  map_zero' := by ext i; rfl
  map_add' x y := by
    ext i
    exact AddCircle.coe_add (p := P) (x i) (y i)

omit [Fintype ι] in
theorem covering_surjective (P : ℝ) : Function.Surjective (covering (ι := ι) P) := by
  intro x
  choose y hy using fun i : ι =>
    (QuotientAddGroup.mk_surjective : Function.Surjective (fun r : ℝ => (r : AddCircle P))) (x i)
  exact ⟨WithLp.toLp 2 y, funext hy⟩

private theorem covering_eq_chart (P : ℝ) :
    (covering (ι := ι) P : EuclideanSpace ℝ ι → (ι → AddCircle P)) =
      HeatTorusGevreyCutoff.chart 0 ∘ PiLp.homeomorph 2 (fun _ : ι => ℝ) := by
  funext x
  simp only [Function.comp_apply, HeatTorusGevreyCutoff.chart, zero_add]
  rfl

theorem covering_isOpenMap (P : ℝ) : IsOpenMap (covering (ι := ι) P) := by
  rw [covering_eq_chart]
  exact (HeatTorusGevreyCutoff.isOpenMap_chart 0).comp (PiLp.homeomorph 2 _).isOpenMap

theorem covering_isQuotientMap (P : ℝ) : IsQuotientMap (covering (ι := ι) P) := by
  let e := PiLp.homeomorph 2 (fun _ : ι => ℝ)
  let c := (0 : ι → AddCircle P)
  have hc : Continuous (covering (ι := ι) P) := by
    rw [covering_eq_chart]
    exact (HeatTorusGevreyCutoff.continuous_chart c).comp e.continuous
  exact (covering_isOpenMap P).isQuotientMap hc (covering_surjective P)

/-- A continuous function invariant under the lattice translations descends
to a continuous function on the physical torus. -/
theorem descend {P : ℝ} {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f)
    (hperiod : ∀ p, covering P p = 0 → ∀ x, f (x + p) = f x) :
    ∃ w : C(ι → AddCircle P, ℝ), ∀ x, w (covering P x) = f x := by
  let r (y : ι → AddCircle P) : EuclideanSpace ℝ ι :=
    Classical.choose (covering_surjective P y)
  have hr (y : ι → AddCircle P) : covering P (r y) = y :=
    Classical.choose_spec (covering_surjective P y)
  let w := f ∘ r
  have hw (x : EuclideanSpace ℝ ι) : w (covering P x) = f x := by
    let p := r (covering P x) - x
    have hp : covering P p = 0 := by
      dsimp only [p]
      rw [map_sub, hr, sub_self]
    change f (r (covering P x)) = f x
    have he : x + p = r (covering P x) := by
      dsimp only [p]
      abel
    simpa only [he] using hperiod p hp x
  have hwc : Continuous w := (covering_isQuotientMap (ι := ι) P).continuous_iff.mpr
    (by rwa [show w ∘ covering P = f from funext hw])
  exact ⟨⟨w, hwc⟩, hw⟩

/-- Differentiation preserves every additive period of a differentiable
function on the Euclidean covering. -/
theorem fderiv_periodic {f : EuclideanSpace ℝ ι → ℝ} (hf : Differentiable ℝ f)
    {p : EuclideanSpace ℝ ι} (hp : ∀ x, f (x + p) = f x) (x : EuclideanSpace ℝ ι) :
    fderiv ℝ f (x + p) = fderiv ℝ f x := by
  have ht := (hasFDerivAt_id (𝕜 := ℝ) x).add_const p
  have h := (hf (x + p)).hasFDerivAt.comp x ht
  have h' : HasFDerivAt f (fderiv ℝ f (x + p)) x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id, hp] using h
  exact h'.fderiv.symm

end HeatFlatTorusSmoothLift

#print axioms HeatFlatTorusSmoothLift.covering_isQuotientMap
#print axioms HeatFlatTorusSmoothLift.descend
#print axioms HeatFlatTorusSmoothLift.fderiv_periodic
