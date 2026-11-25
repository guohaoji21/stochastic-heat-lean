import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace HeatAnalyticCauchyInterpolation

open Finset Lagrange Metric Polynomial Set

private theorem sum_weights {K ι : Type*} [Field K] [DecidableEq ι] {s : Finset ι}
    {v : ι → K} (hs : s.Nonempty) (hv : Set.InjOn v s) {z : K} (hz : ∀ i ∈ s, z ≠ v i) :
    ∑ i ∈ s, nodalWeight s v i * (z - v i)⁻¹ = ((nodal s v).eval z)⁻¹ := by
  have hne := eval_nodal_not_at_node hz
  have h := congrArg (Polynomial.eval z) (sum_basis hv hs)
  simp only [eval_finsetSum, eval_one] at h
  apply mul_left_cancel₀ hne
  rw [mul_inv_cancel₀ hne, mul_sum]
  exact (sum_congr rfl fun i hi => (eval_basis_not_at_node hi (hz i hi)).symm).trans h

/-- Decomposition of the Cauchy kernel into its Lagrange interpolant and
the nodal-factor remainder. -/
theorem kernel_decomposition {K ι : Type*} [Field K] [DecidableEq ι] {s : Finset ι}
    {v : ι → K} (hs : s.Nonempty) (hv : Set.InjOn v s) {w z : K} (hzw : z ≠ w)
    (hw : ∀ i ∈ s, w ≠ v i) (hz : ∀ i ∈ s, z ≠ v i) :
    (z - w)⁻¹ - ∑ i ∈ s, (Lagrange.basis s v i).eval w * (z - v i)⁻¹ =
      (nodal s v).eval w / ((z - w) * (nodal s v).eval z) := by
  let Q := nodal s v
  have hzw₀ := sub_ne_zero.mpr hzw
  have hw₀ := eval_nodal_not_at_node hw
  have hz₀ := eval_nodal_not_at_node hz
  have hterm (i : ι) (hi : i ∈ s) :
      (z - w) * ((Lagrange.basis s v i).eval w * (z - v i)⁻¹) =
        Q.eval w * (nodalWeight s v i * (w - v i)⁻¹ - nodalWeight s v i * (z - v i)⁻¹) := by
    rw [eval_basis_not_at_node hi (hw i hi)]
    field_simp [sub_ne_zero.mpr (hw i hi), sub_ne_zero.mpr (hz i hi)]
    ring
  apply mul_left_cancel₀ hzw₀
  rw [mul_sub, mul_inv_cancel₀ hzw₀, mul_sum, sum_congr rfl hterm,
    ← mul_sum, sum_sub_distrib, sum_weights hs hv hw, sum_weights hs hv hz]
  field_simp [hzw₀, hw₀, hz₀]
  ring

/-- The Cauchy integral expression for the error of Lagrange interpolation
applies to Banach-valued holomorphic functions. -/
theorem cauchy_remainder {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [DecidableEq ι] {s : Finset ι} {v : ι → ℂ}
    {f : ℂ → E} {c w : ℂ} {R : ℝ} (hs : s.Nonempty) (hv : Set.InjOn v s)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) (hvn : ∀ i ∈ s, v i ∈ ball c R)
    (hwn : ∀ i ∈ s, w ≠ v i) :
    f w - ∑ i ∈ s, (Lagrange.basis s v i).eval w • f (v i) =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(c, R),
        ((nodal s v).eval w / ((z - w) * (nodal s v).eval z)) • f z := by
  let K := (2 * (Real.pi : ℂ) * Complex.I)
  let F := fun u z : ℂ => (z - u)⁻¹ • f z
  let a := fun i : ι => (Lagrange.basis s v i).eval w
  have hR : 0 < R := dist_nonneg.trans_lt hw
  have hne {u z : ℂ} (hu : u ∈ ball c R) (hz : z ∈ sphere c R) : z ≠ u :=
    ne_of_mem_of_not_mem hz (ne_of_lt hu)
  have hF {u : ℂ} (hu : u ∈ ball c R) : ContinuousOn (F u) (sphere c R) :=
    ((continuousOn_id.sub continuousOn_const).inv₀ (fun _ hz => sub_ne_zero.mpr (hne hu hz))).smul
      (hf.continuousOn.mono sphere_subset_closedBall)
  have hterm (i : ι) (hi : i ∈ s) : ContinuousOn (fun z => a i • F (v i) z) (sphere c R) :=
    continuousOn_const.smul (hF (hvn i hi))
  have hS : CircleIntegrable (fun z => ∑ i ∈ s, a i • F (v i) z) c R :=
    (continuousOn_finsetSum s hterm).circleIntegrable hR.le
  have hsplit : EqOn (fun z => ((nodal s v).eval w / ((z - w) * (nodal s v).eval z)) • f z)
      (fun z => F w z - ∑ i ∈ s, a i • F (v i) z) (sphere c R) := by
    intro z hz
    dsimp only
    rw [← kernel_decomposition hs hv (hne hw hz) hwn (fun i hi => hne (hvn i hi) hz)]
    simp only [F, a, sub_smul, sum_smul, mul_smul]
  rw [circleIntegral.integral_congr hR.le hsplit, circleIntegral.integral_sub ((hF hw).circleIntegrable hR.le) hS,
    circleIntegral.integral_fun_sum (fun i hi => (hterm i hi).circleIntegrable hR.le)]
  change _ = K⁻¹ • ((∮ z in C(c, R), F w z) - ∑ i ∈ s, ∮ z in C(c, R), a i • F (v i) z)
  have hC (u : ℂ) (hu : u ∈ ball c R) : (∮ z in C(c, R), F u z) = K • f u :=
    hf.circleIntegral_sub_inv_smul hu
  have hk : K ≠ 0 := by simp [K, Real.pi_ne_zero, Complex.I_ne_zero]
  have hterms : (∑ i ∈ s, ∮ z in C(c, R), a i • F (v i) z) =
      ∑ i ∈ s, K • (a i • f (v i)) := by
    refine sum_congr rfl fun i hi => ?_
    rw [circleIntegral.integral_smul, hC _ (hvn i hi), smul_comm]
  rw [hC _ hw, hterms, ← Finset.smul_sum, ← smul_sub, inv_smul_smul₀ hk]

/-- A uniform remainder estimate from the distances between the circle,
the evaluation point, and the interpolation nodes. -/
theorem norm_remainder_le {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [DecidableEq ι] {s : Finset ι} {v : ι → ℂ}
    {f : ℂ → E} {c w : ℂ} {R A δ D M : ℝ} (hs : s.Nonempty) (hv : Set.InjOn v s)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) (hvn : ∀ i ∈ s, v i ∈ ball c R)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hδ : 0 < δ) (hD : 0 < D)
    (hfM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hA_bound : ∀ i ∈ s, ‖w - v i‖ ≤ A)
    (hδ_bound : ∀ z ∈ sphere c R, δ ≤ ‖z - w‖)
    (hD_bound : ∀ z ∈ sphere c R, ∀ i ∈ s, D ≤ ‖z - v i‖) :
    ‖f w - ∑ i ∈ s, (Lagrange.basis s v i).eval w • f (v i)‖ ≤
      R * (A ^ s.card / (δ * D ^ s.card) * M) := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  by_cases h : ∀ i ∈ s, w ≠ v i
  · rw [cauchy_remainder hs hv hf hw hvn h]
    apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    intro z hz
    have hnum : ‖(nodal s v).eval w‖ ≤ A ^ s.card := by
      rw [eval_nodal, norm_prod, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hA_bound
    have hden : D ^ s.card ≤ ‖(nodal s v).eval z‖ := by
      rw [eval_nodal, norm_prod, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => hD.le) (hD_bound z hz)
    rw [norm_smul, norm_div, norm_mul]
    exact mul_le_mul (div_le_div₀ (by positivity) hnum (by positivity)
      (mul_le_mul (hδ_bound z hz) hden (by positivity) (norm_nonneg _))) (hfM z hz)
      (norm_nonneg _) (by positivity)
  · push Not at h
    obtain ⟨i, hi, rfl⟩ := h
    rw [← Finset.add_sum_erase _ _ hi, eval_basis_self hv hi, one_smul]
    have hz : (∑ j ∈ s.erase i, (Lagrange.basis s v j).eval (v i) • f (v j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [eval_basis_of_ne (Finset.mem_erase.mp hj).1 hi, zero_smul]
    rw [hz, add_zero, sub_self, norm_zero]
    positivity

theorem geometric_remainder {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [DecidableEq ι] {s : Finset ι} {v : ι → ℂ} {n : ℕ} {f : ℂ → E} {c w : ℂ}
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (hs : s.Nonempty) (hn : s.card = n + 1)
    (hv : Set.InjOn v s) (hf : DifferentiableOn ℂ f (closedBall c (100 * r)))
    (hw : ‖w - c‖ ≤ 2 * r) (hvn : ∀ i ∈ s, ‖v i - c‖ ≤ r)
    (hM_bound : ∀ z ∈ sphere c (100 * r), ‖f z‖ ≤ M) :
    ‖f w - ∑ i ∈ s, (Lagrange.basis s v i).eval w • f (v i)‖ ≤ M * (1 / 16 : ℝ) ^ n := by
  have hwb : w ∈ ball c (100 * r) := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hvb (i : ι) (hi : i ∈ s) : v i ∈ ball c (100 * r) := by
    rw [mem_ball, dist_eq_norm]
    linarith [hvn i hi]
  have hA (i : ι) (hi : i ∈ s) : ‖w - v i‖ ≤ 3 * r := by
    have h := norm_sub_le (w - c) (v i - c)
    rw [sub_sub_sub_cancel_right] at h
    linarith [hvn i hi]
  have hδ (z : ℂ) (hz : z ∈ sphere c (100 * r)) : 98 * r ≤ ‖z - w‖ := by
    have h := norm_add_le (z - w) (w - c)
    rw [sub_add_sub_cancel] at h
    rw [mem_sphere, dist_eq_norm] at hz
    linarith
  have hD (z : ℂ) (hz : z ∈ sphere c (100 * r)) (i : ι) (hi : i ∈ s) : 99 * r ≤ ‖z - v i‖ := by
    have h := norm_add_le (z - v i) (v i - c)
    rw [sub_add_sub_cancel] at h
    rw [mem_sphere, dist_eq_norm] at hz
    linarith [hvn i hi]
  have hrem := norm_remainder_le hs hv hf hwb hvb hM (by positivity) (by positivity) (by positivity)
    hM_bound hA hδ hD
  rw [hn] at hrem
  have hratio : 3 * r / (99 * r) = (1 / 33 : ℝ) := by
    field_simp
    norm_num
  have hrad : 100 * r / (98 * r) = (50 / 49 : ℝ) := by
    field_simp
    norm_num
  calc
    _ ≤ (100 * r) * ((3 * r) ^ (n + 1) / ((98 * r) * (99 * r) ^ (n + 1)) * M) := hrem
    _ = (100 * r / (98 * r)) * (3 * r / (99 * r)) ^ (n + 1) * M := by
      rw [div_pow]
      field_simp
    _ ≤ M * (1 / 16 : ℝ) ^ n := by
      rw [hrad, hratio, pow_succ]
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 33)
        (by norm_num : (1 / 33 : ℝ) ≤ 1 / 16) n
      calc
        _ = (50 / (49 * 33) : ℝ) * (M * (1 / 33 : ℝ) ^ n) := by ring
        _ ≤ M * (1 / 33 : ℝ) ^ n := mul_le_of_le_one_left (by positivity) (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hM

end HeatAnalyticCauchyInterpolation

#print axioms HeatAnalyticCauchyInterpolation.kernel_decomposition
#print axioms HeatAnalyticCauchyInterpolation.cauchy_remainder
#print axioms HeatAnalyticCauchyInterpolation.norm_remainder_le
#print axioms HeatAnalyticCauchyInterpolation.geometric_remainder
