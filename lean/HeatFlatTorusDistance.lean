import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace HeatFlatTorusDistance

open Set

variable {ι : Type*} [Fintype ι]

/-- The Euclidean product of the shortest coordinate distances, in the
physical coordinates of the period-`P` torus. -/
def distance {P : ℝ} (x y : ι → AddCircle P) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => dist (x i) (y i)) : EuclideanSpace ℝ ι)‖

theorem distance_eq_sqrt {P : ℝ} (x y : ι → AddCircle P) :
    distance x y = Real.sqrt (∑ i, dist (x i) (y i) ^ 2) := by
  simp [distance, PiLp.norm_eq_of_L2, Real.norm_eq_abs]

theorem distance_triangle {P : ℝ} (x y z : ι → AddCircle P) :
    distance x z ≤ distance x y + distance y z := by
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => dist (x i) (y i))
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => dist (y i) (z i))
  refine le_trans ?_ (norm_add_le a b)
  rw [distance_eq_sqrt, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simpa only [a, b, PiLp.add_apply, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist (x i) (z i))
      (dist_triangle (x i) (y i) (z i)) 2

private theorem circle_distance_formula (P u v : ℝ) :
    dist (u : AddCircle P) (v : AddCircle P) = |u - v - round (P⁻¹ * (u - v)) * P| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq]

/-- The physical distance is attained by choosing the nearest integer
period shift independently in every coordinate. -/
theorem nearest_lift (P : ℝ) (x y : ι → ℝ) :
    distance (fun i => (x i : AddCircle P)) (fun i => (y i : AddCircle P)) =
      Real.sqrt (∑ i, (x i - y i - round (P⁻¹ * (x i - y i)) * P) ^ 2) := by
  simp only [distance_eq_sqrt, circle_distance_formula, sq_abs]

/-- Every lift of a displacement bounds the physical distance from above. -/
theorem le_lift {P : ℝ} (hP : 0 < P) (x y : ι → ℝ) (k : ι → ℤ) :
    distance (fun i => (x i : AddCircle P)) (fun i => (y i : AddCircle P)) ≤
      Real.sqrt (∑ i, (x i - y i - k i * P) ^ 2) := by
  rw [nearest_lift]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  let u := x i - y i
  have hk (n : ℤ) : P * |P⁻¹ * u - n| = |u - n * P| := calc
    _ = |P| * |P⁻¹ * u - n| := by rw [abs_of_pos hP]
    _ = |P * (P⁻¹ * u - n)| := (abs_mul _ _).symm
    _ = _ := by
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hP.ne', one_mul, mul_comm P (n : ℝ)]
  have h := mul_le_mul_of_nonneg_left (round_le (P⁻¹ * u) (k i)) hP.le
  rw [hk, hk] at h
  simpa only [u, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Distance to a support set in the physical torus distance. -/
def distanceTo {P : ℝ} (D : Set (ι → AddCircle P)) (x : ι → AddCircle P) : ℝ :=
  sInf (distance x '' D)

private theorem distance_nonneg {P : ℝ} (x y : ι → AddCircle P) : 0 ≤ distance x y :=
  norm_nonneg _

theorem distanceTo_nonneg {P : ℝ} {D : Set (ι → AddCircle P)} (hD : D.Nonempty)
    (x : ι → AddCircle P) : 0 ≤ distanceTo D x := by
  refine le_csInf (hD.image (distance x)) ?_
  rintro _ ⟨y, _, rfl⟩
  exact distance_nonneg _ _

theorem distanceTo_le {P : ℝ} {D : Set (ι → AddCircle P)} {y : ι → AddCircle P}
    (hy : y ∈ D) (x : ι → AddCircle P) : distanceTo D x ≤ distance x y := by
  apply csInf_le _ (mem_image_of_mem (distance x) hy)
  refine ⟨0, ?_⟩
  rintro _ ⟨z, _, rfl⟩
  exact distance_nonneg _ _

theorem distanceTo_eq_zero {P : ℝ} {D : Set (ι → AddCircle P)} {x : ι → AddCircle P}
    (hx : x ∈ D) : distanceTo D x = 0 := by
  apply le_antisymm _ (distanceTo_nonneg ⟨x, hx⟩ x)
  simpa [distance_eq_sqrt] using distanceTo_le hx x

theorem le_distanceTo {P δ : ℝ} {D : Set (ι → AddCircle P)} (hD : D.Nonempty)
    (x : ι → AddCircle P) (h : ∀ y ∈ D, δ ≤ distance x y) : δ ≤ distanceTo D x := by
  refine le_csInf (hD.image (distance x)) ?_
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

private theorem distanceTo_sub_le {P : ℝ} {D : Set (ι → AddCircle P)} (hD : D.Nonempty)
    (x y : ι → AddCircle P) : distanceTo D x - distanceTo D y ≤ distance x y := by
  have h : distanceTo D x - distance x y ≤ distanceTo D y := by
    apply le_distanceTo hD
    intro z hz
    linarith [(distanceTo_le hz x).trans (distance_triangle x y z)]
  linarith

/-- The periodic lift of the distance to the support set has Euclidean
Lipschitz constant one in the physical coordinates. -/
theorem lipschitz_distanceTo_lift {P : ℝ} (hP : 0 < P)
    {D : Set (ι → AddCircle P)} (hD : D.Nonempty) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ ι => distanceTo D (fun i => (x i : AddCircle P))) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  let u : ι → AddCircle P := fun i => (x i : AddCircle P)
  let v : ι → AddCircle P := fun i => (y i : AddCircle P)
  have hb (x y : EuclideanSpace ℝ ι) :
      distance (fun i => (x i : AddCircle P)) (fun i => (y i : AddCircle P)) ≤ dist x y := by
    simpa only [Int.cast_zero, zero_mul, sub_zero, PiLp.dist_eq_of_L2, Real.dist_eq, sq_abs] using
      (le_lift hP (fun i => x i) (fun i => y i) (fun _ => 0))
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  change |distanceTo D u - distanceTo D v| ≤ dist x y
  apply abs_le.mpr
  exact ⟨by linarith [(distanceTo_sub_le hD v u).trans ((hb y x).trans_eq (dist_comm y x))],
    (distanceTo_sub_le hD u v).trans (hb x y)⟩

end HeatFlatTorusDistance

#print axioms HeatFlatTorusDistance.distance_triangle
#print axioms HeatFlatTorusDistance.le_lift
#print axioms HeatFlatTorusDistance.lipschitz_distanceTo_lift
