import HeatAnalyticCauchyInterpolation
import HeatAnalyticInterpolationBalance
import HeatEquispacedLagrangeDenominator
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace HeatAnalyticLocalPropagation

open Finset Metric Polynomial

private def step (r : ℝ) (n : ℕ) : ℝ := 2 * r / n

private def node (c : ℂ) (r : ℝ) (n j : ℕ) : ℂ := c + ((step r n * j - r : ℝ) : ℂ)

private theorem step_pos {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) : 0 < step r n := by
  have : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold step
  positivity

private theorem offset_abs {r : ℝ} (hr : 0 < r) {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ n) :
    |step r n * j - r| ≤ r := by
  have hd := step_pos hr hn
  have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hend : step r n * n = 2 * r := div_mul_cancel₀ _ hnz
  have hle : step r n * j ≤ step r n * n := mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hd.le
  have hnon : 0 ≤ step r n * j := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem node_dist (c : ℂ) {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) (i j : ℕ) :
    ‖node c r n i - node c r n j‖ = step r n * |(i : ℝ) - j| := by
  have he : node c r n i - node c r n j = ((step r n * ((i : ℝ) - j) : ℝ) : ℂ) := by
    simp only [node, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (step_pos hr hn)]

private theorem basis_bound (c w : ℂ) {r : ℝ} (hr : 0 < r) {n i : ℕ} (hn : 1 ≤ n)
    (hi : i ∈ range (n + 1)) (hw : ‖w - c‖ ≤ 2 * r) :
    ‖(Lagrange.basis (range (n + 1)) (node c r n) i).eval w‖ ≤
      (3 * (n : ℝ) / 2) ^ n / ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) := by
  let s := (range (n + 1)).erase i
  let v := node c r n
  have hs : s.card = n := by simp [s, card_erase_of_mem hi]
  have hv (j : ℕ) (hj : j ∈ s) : ‖w - v j‖ ≤ 3 * r := by
    have hj' : j ≤ n := by have := mem_range.mp (mem_of_mem_erase hj); omega
    have hjc : ‖c - v j‖ ≤ r := by
      have h : v j - c = ((step r n * j - r : ℝ) : ℂ) := by simp [v, node]
      rw [norm_sub_rev, h, Complex.norm_real, Real.norm_eq_abs]
      exact offset_abs hr hn hj'
    have hd := norm_add_le (w - c) (c - v j)
    rw [sub_add_sub_cancel] at hd
    linarith
  have hP : (∏ j ∈ s, ‖w - v j‖) ≤ (3 * r) ^ n := by
    calc
      _ ≤ ∏ _j ∈ s, (3 * r) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hv
      _ = _ := by rw [Finset.prod_const, hs]
  have hD : (∏ j ∈ s, ‖v i - v j‖) =
      step r n ^ n * ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) := by
    have hi' : i ≤ n := by have := mem_range.mp hi; omega
    simp only [v, node_dist c hr hn, Finset.prod_mul_distrib, Finset.prod_const, hs]
    rw [HeatEquispacedLagrangeDenominator.denominator_real n i hi']
  have hdn : 0 < step r n := step_pos hr hn
  have hiF : 0 < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hnF : 0 < ((n - i).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - i)
  have hratio : 3 * r / step r n = 3 * (n : ℝ) / 2 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    unfold step
    field_simp
  simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X,
    norm_prod, norm_mul, norm_inv]
  change (∏ j ∈ s, ‖v i - v j‖⁻¹ * ‖w - v j‖) ≤ _
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hD]
  calc
    _ ≤ (step r n ^ n * ((i.factorial : ℝ) * ((n - i).factorial : ℝ)))⁻¹ * (3 * r) ^ n :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    _ = (3 * r / step r n) ^ n / ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) := by
      rw [div_pow, div_div, div_eq_inv_mul]
    _ = _ := by rw [hratio]

private theorem sum_basis_bound (c w : ℂ) {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n)
    (hw : ‖w - c‖ ≤ 2 * r) :
    ∑ i ∈ range (n + 1), ‖(Lagrange.basis (range (n + 1)) (node c r n) i).eval w‖ ≤ (16 : ℝ) ^ n := by
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hchoose (i : ℕ) (hi : i ∈ range (n + 1)) :
      (3 * (n : ℝ) / 2) ^ n / ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) =
      (3 * (n : ℝ) / 2) ^ n / (n.factorial : ℝ) * (n.choose i : ℝ) := by
    have hi' : i ≤ n := by have := mem_range.mp hi; omega
    have hnC : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) = (n.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
    have hiF : 0 < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hnF : 0 < ((n - i).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - i)
    rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hiF.ne' hnF.ne') hfac.ne']
    rw [← hnC]
    ring
  calc
    _ ≤ ∑ i ∈ range (n + 1), (3 * (n : ℝ) / 2) ^ n / ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) :=
      Finset.sum_le_sum fun i hi => basis_bound c w hr hn hi hw
    _ = ∑ i ∈ range (n + 1), (3 * (n : ℝ) / 2) ^ n / (n.factorial : ℝ) * (n.choose i : ℝ) :=
      Finset.sum_congr rfl hchoose
    _ = (3 : ℝ) ^ n * ((n : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [← Finset.mul_sum, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      rw [div_pow, mul_pow]
      field_simp
    _ ≤ (3 : ℝ) ^ n * Real.exp n := mul_le_mul_of_nonneg_left
      (Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n) (by positivity)
    _ = (3 * Real.exp 1) ^ n := by rw [mul_pow, ← Real.exp_nat_mul, mul_one]
    _ ≤ (16 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_one_lt_three]) _

/-- A bound on a real segment controls a larger complex disk inside a disk
on which the holomorphic function has a uniform bound. -/
theorem segment_to_disk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {c w : ℂ} {r M ε : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hf : DifferentiableOn ℂ f (closedBall c (100 * r)))
    (hcap : ∀ z ∈ closedBall c (100 * r), ‖f z‖ ≤ M)
    (hsegment : ∀ t : ℝ, |t| ≤ r → ‖f (c + (t : ℂ))‖ ≤ ε)
    (hw : ‖w - c‖ ≤ 2 * r) : ‖f w‖ ≤ 17 * Real.sqrt (M * ε) := by
  have hwcap : ‖f w‖ ≤ M := hcap w (by rw [mem_closedBall, dist_eq_norm]; linarith)
  have h := HeatAnalyticInterpolationBalance.sqrt_bound (q := 1 / 16)
    (by norm_num) (by norm_num) hM hε hwcap ?_
  · norm_num at h
    exact h
  intro n hn
  let s := range (n + 1)
  let v := node c r n
  let p := ∑ i ∈ s, (Lagrange.basis s v i).eval w • f (v i)
  have hv : Set.InjOn v s := by
    intro i _ j _ hij
    have hd := node_dist c hr hn i j
    change node c r n i = node c r n j at hij
    rw [hij, sub_self, norm_zero, eq_comm, mul_eq_zero] at hd
    have hz : |(i : ℝ) - j| = 0 := hd.resolve_left (step_pos hr hn).ne'
    exact_mod_cast sub_eq_zero.mp (abs_eq_zero.mp hz)
  have hnodes (j : ℕ) (hj : j ∈ s) : ‖v j - c‖ ≤ r := by
    have hj' : j ≤ n := by have := mem_range.mp hj; omega
    have h : v j - c = ((step r n * j - r : ℝ) : ℂ) := by simp [v, node]
    rw [h, Complex.norm_real, Real.norm_eq_abs]
    exact offset_abs hr hn hj'
  have hfnode (j : ℕ) (hj : j ∈ s) : ‖f (v j)‖ ≤ ε :=
    hsegment _ (offset_abs hr hn (by have := mem_range.mp hj; omega))
  have hrem : ‖f w - p‖ ≤ M * (1 / 16 : ℝ) ^ n :=
    HeatAnalyticCauchyInterpolation.geometric_remainder hr hM (by simp [s]) (by simp [s])
      hv hf hw hnodes (fun z hz => hcap z (sphere_subset_closedBall hz))
  have hp : ‖p‖ ≤ (16 : ℝ) ^ n * ε := by
    calc
      _ ≤ ∑ i ∈ s, ‖(Lagrange.basis s v i).eval w‖ * ‖f (v i)‖ := by
        simpa only [norm_smul] using norm_sum_le s (fun i => (Lagrange.basis s v i).eval w • f (v i))
      _ ≤ ∑ i ∈ s, ‖(Lagrange.basis s v i).eval w‖ * ε := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hfnode i hi) (norm_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (sum_basis_bound c w hr hn hw) hε
  have htri := norm_add_le (f w - p) p
  rw [sub_add_cancel] at htri
  calc
    _ ≤ M * (1 / 16 : ℝ) ^ n + (16 : ℝ) ^ n * ε := htri.trans (add_le_add hrem hp)
    _ = _ := by
      have hi : ((1 / 16 : ℝ) ^ n)⁻¹ = (16 : ℝ) ^ n := by
        rw [← inv_pow, show (1 / 16 : ℝ)⁻¹ = 16 by norm_num]
      have he := (div_eq_inv_mul ε ((1 / 16 : ℝ) ^ n)).trans (congrArg (· * ε) hi)
      rw [he, add_comm]

end HeatAnalyticLocalPropagation

#print axioms HeatAnalyticLocalPropagation.segment_to_disk
