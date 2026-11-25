import HeatFlatTorusDistance
import HeatFlatTorusSmoothLift
import HeatLipschitzMollifier
import HeatTorusInitialData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatFlatTorusDistanceWeight

open MeasureTheory UnitAddTorus HeatFlatTorusSmoothLift HeatFlatTorusDistance
open HeatTorusInitialData (rescale rescale_coe)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem covering_rescale {P : ℝ} (hP : 0 < P) (x : EuclideanSpace ℝ ι) :
    covering P (P • x) = rescale hP (covering 1 x) := by
  funext i
  rw [show rescale hP (covering 1 x) i = _ from rescale_coe hP (fun j => x j) i]
  change ((P * x i : ℝ) : AddCircle P) = ((x i * P : ℝ) : AddCircle P)
  rw [mul_comm P]

omit [Fintype ι] in
private theorem covering_axis (i : ι) (t : ℝ) :
    covering 1 (t • EuclideanSpace.single i 1) = Pi.single i (t : UnitAddCircle) := by
  funext j
  change (((t • EuclideanSpace.single i 1 : EuclideanSpace ℝ ι) j : ℝ) : UnitAddCircle) = _
  rw [PiLp.smul_apply]
  change ((t * (PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ ι) j : ℝ) : UnitAddCircle) = _
  rw [PiLp.single_apply]
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single, h]

/-- The geodesic distance to a nonempty set admits smooth, periodic
approximants with the same Euclidean gradient bound in physical coordinates. -/
theorem exists_distance_approx {P ε : ℝ} (hP : 0 < P) (hε : 0 < ε)
    {D : Set (ι → AddCircle P)} (hD : D.Nonempty) :
    ∃ (φ : C(UnitAddTorus ι, ℝ)) (dφ : ι → C(UnitAddTorus ι, ℝ)),
      (∀ x, |φ x - distanceTo D (rescale hP x)| ≤ ε) ∧
      (∀ x, ∑ i, (dφ i x) ^ 2 ≤ 1) ∧
      (∀ i (x : UnitAddTorus ι) (t : ℝ),
        HasDerivAt (fun s : ℝ => φ (x + Pi.single i (s : UnitAddCircle)))
          (P * dφ i (x + Pi.single i (t : UnitAddCircle))) t) := by
  let f (x : EuclideanSpace ℝ ι) := distanceTo D (covering P x)
  have hf : LipschitzWith 1 f := lipschitz_distanceTo_lift hP hD
  obtain ⟨g, hg, hlip, herr, hper⟩ :=
    HeatLipschitzMollifier.exists_smooth_periodic_approx volume hf hε
  have hperg (p : EuclideanSpace ℝ ι) (hp : covering P p = 0) (x : EuclideanSpace ℝ ι) :
      g (x + p) = g x := hper p (fun y => by simp [f, map_add, hp]) x
  obtain ⟨w, hw⟩ := descend hg.continuous hperg
  let coordinate (i : ι) (x : EuclideanSpace ℝ ι) :=
    fderiv ℝ g x (EuclideanSpace.single i 1)
  have hcoordinate (i : ι) : Continuous (coordinate i) := by
    exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hperiod (i : ι) (p : EuclideanSpace ℝ ι) (hp : covering P p = 0)
      (x : EuclideanSpace ℝ ι) : coordinate i (x + p) = coordinate i x := by
    dsimp only [coordinate]
    rw [fderiv_periodic (hg.differentiable (by simp)) (hperg p hp)]
  choose dw hdw using fun i => descend (hcoordinate i) (hperiod i)
  let φ : C(UnitAddTorus ι, ℝ) := w.comp ⟨rescale hP, (rescale hP).continuous⟩
  let dφ (i : ι) : C(UnitAddTorus ι, ℝ) :=
    (dw i).comp ⟨rescale hP, (rescale hP).continuous⟩
  refine ⟨φ, dφ, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨v, rfl⟩ := covering_surjective 1 x
    change |w (rescale hP (covering 1 v)) - distanceTo D (rescale hP (covering 1 v))| ≤ ε
    rw [← covering_rescale hP, hw]
    exact herr (P • v)
  · intro x
    obtain ⟨v, rfl⟩ := covering_surjective 1 x
    change ∑ i, (dw i (rescale hP (covering 1 v))) ^ 2 ≤ 1
    simp_rw [← covering_rescale hP, hdw]
    exact HeatLipschitzMollifier.gradient_sq_le_one hlip (P • v)
  · intro i x t
    obtain ⟨v, rfl⟩ := covering_surjective 1 x
    let e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
    have hpath (s : ℝ) : covering 1 v + Pi.single i (s : UnitAddCircle) =
        covering 1 (v + s • e) := by
      rw [map_add, covering_axis]
    have heq (s : ℝ) : φ (covering 1 v + Pi.single i (s : UnitAddCircle)) =
        g (P • (v + s • e)) := by
      change w (rescale hP (covering 1 v + Pi.single i (s : UnitAddCircle))) = _
      rw [hpath, ← covering_rescale hP, hw]
    have heq' : dφ i (covering 1 v + Pi.single i (t : UnitAddCircle)) =
        coordinate i (P • (v + t • e)) := by
      change dw i (rescale hP (covering 1 v + Pi.single i (t : UnitAddCircle))) = _
      rw [hpath, ← covering_rescale hP, hdw]
    simp_rw [heq, heq']
    have hlinear : HasDerivAt (fun s : ℝ => P • (v + s • e)) (P • e) t := by
      have h := (((hasDerivAt_id t).smul_const e).const_add v).const_smul P
      rw [one_smul] at h
      exact h
    have hdiff := ((hg.differentiable (by simp)) (P • (v + t • e))).hasFDerivAt
    have hcomp := hdiff.comp_hasDerivAt t hlinear
    rw [map_smul, smul_eq_mul] at hcomp
    exact hcomp

end HeatFlatTorusDistanceWeight

#print axioms HeatFlatTorusDistanceWeight.exists_distance_approx
