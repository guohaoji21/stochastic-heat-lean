import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace HeatPartitionDecay

/-- The exponential factor in the paper's recursive time partition. -/
theorem recurrence_exp (κ x y : ℝ) (hx : 0 < x)
    (h : κ * (y - x) = Real.log (2 * x)) :
    Real.exp (-κ * y) * x = Real.exp (-κ * x) / 2 := by
  have hpos : 0 < 2 * x := by positivity
  have hexp : Real.exp (κ * (y - x)) = 2 * x := by
    rw [h, Real.exp_log hpos]
  have hrewrite : -κ * y = -κ * x - κ * (y - x) := by ring
  rw [hrewrite, Real.exp_sub]
  rw [hexp]
  field_simp

/-- Equation at line 113, indexed from zero instead of one. -/
theorem recurrence_product (κ : ℝ) (ell : ℕ → ℝ)
    (hpos : ∀ n, 0 < ell n)
    (hrec : ∀ n, κ * (ell (n + 1) - ell n) = Real.log (2 * ell n)) :
    ∀ n : ℕ, Real.exp (-κ * ell n) * (∏ i ∈ Finset.range n, ell i) =
      Real.exp (-κ * ell 0) / (2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, pow_succ]
      calc
        Real.exp (-κ * ell (n + 1)) * ((∏ i ∈ Finset.range n, ell i) * ell n) =
            (Real.exp (-κ * ell (n + 1)) * ell n) * (∏ i ∈ Finset.range n, ell i) := by ring
        _ = (Real.exp (-κ * ell n) / 2) * (∏ i ∈ Finset.range n, ell i) := by
          rw [recurrence_exp κ (ell n) (ell (n + 1)) (hpos n) (hrec n)]
        _ = (Real.exp (-κ * ell n) * (∏ i ∈ Finset.range n, ell i)) / 2 := by ring
        _ = Real.exp (-κ * ell 0) / (2 : ℝ) ^ n / 2 := by rw [ih]
        _ = Real.exp (-κ * ell 0) / ((2 : ℝ) ^ n * 2) := by ring

/-- The geometric estimate used to sum the observation bound. -/
theorem recurrence_sum_bound (κ : ℝ) (ell : ℕ → ℝ)
    (hpos : ∀ n, 0 < ell n)
    (hrec : ∀ n, κ * (ell (n + 1) - ell n) = Real.log (2 * ell n))
    (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.exp (-κ * ell n) * (∏ i ∈ Finset.range n, ell i)) ≤
      2 * Real.exp (-κ * ell 0) := by
  have heq : (∑ n ∈ Finset.range N, Real.exp (-κ * ell n) * (∏ i ∈ Finset.range n, ell i)) =
      Real.exp (-κ * ell 0) * (∑ n ∈ Finset.range N, ((1 : ℝ) / 2) ^ n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [recurrence_product κ ell hpos hrec n]
    simp [div_eq_mul_inv, inv_pow]
  rw [heq]
  have hbound := sum_geometric_two_le N
  have hmul := mul_le_mul_of_nonneg_left hbound (le_of_lt (Real.exp_pos (-κ * ell 0)))
  linarith

end HeatPartitionDecay

#check @HeatPartitionDecay.recurrence_exp
#print axioms HeatPartitionDecay.recurrence_exp

#check @HeatPartitionDecay.recurrence_product
#print axioms HeatPartitionDecay.recurrence_product

#check @HeatPartitionDecay.recurrence_sum_bound
#print axioms HeatPartitionDecay.recurrence_sum_bound
