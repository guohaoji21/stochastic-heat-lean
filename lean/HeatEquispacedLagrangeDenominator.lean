import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace HeatEquispacedLagrangeDenominator

open Finset

private def gap (j k : ℕ) : ℕ := if k = j then 1 else (j - k) + (k - j)

private theorem descending_factorial (n : ℕ) : (∏ k ∈ range n, (n - k)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ']
    have h : (∏ k ∈ range n, ((n + 1) - (k + 1))) = ∏ k ∈ range n, (n - k) := by
      apply prod_congr rfl
      intro k _
      omega
    rw [h, ih]
    simp [Nat.factorial_succ, mul_comm]

private theorem full_gap_product (j m : ℕ) :
    (∏ k ∈ range (j + m + 1), gap j k) = j.factorial * m.factorial := by
  have hl : (∏ k ∈ range j, gap j k) = j.factorial := by
    rw [← descending_factorial j]
    apply prod_congr rfl
    intro k hk
    have hkj := mem_range.mp hk
    simp [gap, ne_of_lt hkj, Nat.sub_eq_zero_of_le hkj.le]
  have hr : (∏ t ∈ range (m + 1), gap j (j + t)) = m.factorial := by
    rw [prod_range_succ']
    have he : (∏ t ∈ range m, gap j (j + (t + 1))) = ∏ t ∈ range m, (t + 1) := by
      apply prod_congr rfl
      intro t _
      have hne : j + (t + 1) ≠ j := by omega
      have hz : j - (j + (t + 1)) = 0 := by omega
      have hd : j + (t + 1) - j = t + 1 := by omega
      simp [gap, hne, hz, hd]
    rw [he, prod_range_add_one_eq_factorial]
    simp [gap]
  rw [Nat.add_assoc, prod_range_add, hl, hr]

theorem denominator_nat (n j : ℕ) (hj : j ≤ n) :
    (∏ k ∈ (range (n + 1)).erase j, ((j - k) + (k - j))) = j.factorial * (n - j).factorial := by
  have hprod : (∏ k ∈ (range (n + 1)).erase j, ((j - k) + (k - j))) =
      ∏ k ∈ (range (n + 1)).erase j, gap j k := by
    apply prod_congr rfl
    intro k hk
    simp [gap, (mem_erase.mp hk).1]
  rw [hprod, ← one_mul (∏ k ∈ (range (n + 1)).erase j, gap j k)]
  nth_rw 1 [show (1 : ℕ) = gap j j by simp [gap]]
  rw [mul_prod_erase _ _ (mem_range.mpr (by omega : j < n + 1))]
  conv_lhs => rw [show n + 1 = j + (n - j) + 1 by omega]
  exact full_gap_product _ _

private theorem abs_gap (j k : ℕ) : |(j : ℝ) - (k : ℝ)| = (((j - k) + (k - j) : ℕ) : ℝ) := by
  rcases le_total j k with h | h
  · have hr : (j : ℝ) ≤ k := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr hr), Nat.sub_eq_zero_of_le h, Nat.zero_add, Nat.cast_sub h]
    ring
  · have hr : (k : ℝ) ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (sub_nonneg.mpr hr), Nat.sub_eq_zero_of_le h, Nat.add_zero, Nat.cast_sub h]

theorem denominator_real (n j : ℕ) (hj : j ≤ n) :
    (∏ k ∈ (range (n + 1)).erase j, |(j : ℝ) - (k : ℝ)|) =
      (j.factorial : ℝ) * ((n - j).factorial : ℝ) := by
  simp_rw [abs_gap]
  exact_mod_cast denominator_nat n j hj

end HeatEquispacedLagrangeDenominator

#print axioms HeatEquispacedLagrangeDenominator.denominator_real
