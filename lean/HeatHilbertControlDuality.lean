import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
noncomputable section

namespace HeatHilbertControlDuality

open Filter InnerProductSpace
open scoped Topology

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- A linear functional bounded by the observation norm is represented by
a control of the same norm, even on a nonclosed observation range. -/
theorem exists_control_of_linear_bound {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    (A : Z →ₗ[ℝ] U) (goal : Z →ₗ[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hobs : ∀ z : Z, |goal z| ≤ C * ‖A z‖) :
    ∃ u : U, (∀ z, inner ℝ u (A z) = goal z) ∧ ‖u‖ ≤ C := by
  let obs := A.rangeRestrict
  have hker : LinearMap.ker obs ≤ LinearMap.ker goal := by
    intro y hy
    have hy' : A y = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hy)
    have h := hobs y
    rw [hy', norm_zero, mul_zero] at h
    exact LinearMap.mem_ker.mpr (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  let f₀ : LinearMap.range A →ₗ[ℝ] ℝ :=
    obs.liftOfSurjective A.surjective_rangeRestrict ⟨goal, hker⟩
  have happly (y : Z) : f₀ (obs y) = goal y :=
    LinearMap.equivOfSurjective_apply A.surjective_rangeRestrict hker
  have hf₀ (v : LinearMap.range A) : ‖f₀ v‖ ≤ C * ‖v‖ := by
    obtain ⟨y, rfl⟩ := A.surjective_rangeRestrict v
    rw [happly, Real.norm_eq_abs]
    exact hobs y
  let f := f₀.mkContinuous C hf₀
  obtain ⟨φ, hφ, hφnorm⟩ := exists_extension_norm_eq (LinearMap.range A) f
  let u := (toDual ℝ U).symm φ
  refine ⟨u, ?_, ?_⟩
  · intro y
    change inner ℝ ((toDual ℝ U).symm φ) ((obs y).val) = goal y
    rw [toDual_symm_apply, hφ]
    exact happly y
  · change ‖(toDual ℝ U).symm φ‖ ≤ C
    rw [LinearIsometryEquiv.norm_map, hφnorm]
    exact f.opNorm_le_bound hC hf₀

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- An estimate on the adjoint of the terminal control map gives an exact
control with the same norm bound. The range of the adjoint may be nonclosed. -/
theorem exists_control_of_adjoint_bound (A : U →L[ℝ] Y) (target : Y) {C : ℝ}
    (hC : 0 ≤ C) (hobs : ∀ y : Y, |inner ℝ target y| ≤ C * ‖A.adjoint y‖) :
    ∃ u : U, A u = target ∧ ‖u‖ ≤ C := by
  obtain ⟨u, hu, hnorm⟩ := exists_control_of_linear_bound A.adjoint.toLinearMap
    (innerSL ℝ target).toLinearMap hC hobs
  refine ⟨u, ?_, hnorm⟩
  apply ext_inner_right ℝ
  intro y
  rw [← A.adjoint_inner_right]
  exact hu y

/-- A uniformly bounded sequence whose terminal values converge weakly
to the target gives an exact control with the same bound. -/
theorem exists_control_of_weak_approx (A : U →L[ℝ] Y) (target : Y) {C : ℝ}
    (hC : 0 ≤ C) (u : ℕ → U) (hu : ∀ n, ‖u n‖ ≤ C)
    (hlim : ∀ y : Y, Tendsto (fun n => inner ℝ (A (u n)) y) atTop (𝓝 (inner ℝ target y))) :
    ∃ x : U, A x = target ∧ ‖x‖ ≤ C := by
  apply exists_control_of_adjoint_bound A target hC
  intro y
  apply le_of_tendsto (hlim y).abs
  apply Eventually.of_forall
  intro n
  rw [← A.adjoint_inner_right]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))

end HeatHilbertControlDuality

#print axioms HeatHilbertControlDuality.exists_control_of_linear_bound
#print axioms HeatHilbertControlDuality.exists_control_of_adjoint_bound
#print axioms HeatHilbertControlDuality.exists_control_of_weak_approx
