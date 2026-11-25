import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace HeatGevreyWidths

open Finset

/-- The width of convolution layer `n`, numbered from zero. -/
def width (a s : ℝ) (n : ℕ) : ℝ := a / ((n + 1 : ℕ) : ℝ) ^ s

theorem width_pos {a : ℝ} (ha : 0 < a) (s : ℝ) (n : ℕ) : 0 < width a s n :=
  div_pos ha (Real.rpow_pos_of_pos (by positivity) _)

theorem width_antitone {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    Antitone (width a s) := by
  intro m n hmn
  exact div_le_div_of_nonneg_left ha (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn) hs)

theorem width_summable (a : ℝ) {s : ℝ} (hs : 1 < s) : Summable (width a s) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) := Real.summable_nat_rpow_inv.mpr hs
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) 1).mpr h
  change Summable (fun n : ℕ => a / ((n + 1 : ℕ) : ℝ) ^ s)
  simpa only [div_eq_mul_inv] using hshift.mul_left a

theorem width_product (a s : ℝ) (n : ℕ) :
    (∏ j ∈ range n, width a s j) = a ^ n / (n.factorial : ℝ) ^ s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, width, div_mul_div_comm, pow_succ, Nat.factorial_succ,
      Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), mul_comm ((↑(n + 1) : ℝ) ^ s)]

/-- The reciprocal widths give the exact factorial power in the derivative estimate. -/
theorem width_product_inv (a s : ℝ) (n : ℕ) :
    (∏ j ∈ range n, width a s j)⁻¹ = (n.factorial : ℝ) ^ s / a ^ n := by
  rw [width_product, inv_div]

theorem exists_width_budget {s δ : ℝ} (hs : 1 < s) (hδ : 0 < δ) :
    ∃ a : ℝ, 0 < a ∧ Summable (width a s) ∧ (∑' n, width a s n) < δ := by
  let total : ℝ := ∑' n, width 1 s n
  have htotal : 0 ≤ total := tsum_nonneg fun n => (width_pos zero_lt_one s n).le
  let a := δ / (total + 1)
  have ha : 0 < a := div_pos hδ (by linarith)
  refine ⟨a, ha, width_summable a hs, ?_⟩
  have hwidth (n : ℕ) : width a s n = a * width 1 s n := by
    simp only [width, div_eq_mul_inv, one_mul]
  simp_rw [hwidth]
  rw [tsum_mul_left]
  change (δ / (total + 1)) * total < δ
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by linarith)).2
  linarith

end HeatGevreyWidths

#print axioms HeatGevreyWidths.width_product_inv
#print axioms HeatGevreyWidths.exists_width_budget
