import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace HeatGevreyFourierDecay

/-- Optimization of the number of integrations by parts in the Gevrey-1
Fourier estimate. The zero frequency is included. -/
theorem exponential_bound (A C ρ ω : ℝ) (hC : 0 ≤ C) (hρ : 0 < ρ) (hω : 0 ≤ ω)
    (h : ∀ n : ℕ, ω^n * A ≤ C * ρ^n * (n.factorial : ℝ)) :
    A ≤ 2 * C * Real.exp (-(Real.log 2 / (2 * ρ)) * ω) := by
  rcases eq_or_lt_of_le hω with hzero | hpos
  · have h₀ : A ≤ C := by simpa using h 0
    rw [← hzero, mul_zero, Real.exp_zero, mul_one]
    linarith
  let q := ω / (2 * ρ)
  let n := ⌊q⌋₊
  have hden : (0 : ℝ) < 2 * ρ := by positivity
  have hn : (n : ℝ) ≤ q := Nat.floor_le (div_nonneg hω hden.le)
  have hq : q < (n : ℝ) + 1 := Nat.lt_floor_add_one q
  have hsmall : ρ * (n : ℝ) ≤ ω / 2 := by
    have hh := (le_div_iff₀ hden).mp hn
    linarith
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
  have hstep : ω^n * A ≤ ω^n * (C * (1 / 2 : ℝ)^n) := by
    calc
      _ ≤ C * ρ^n * (n.factorial : ℝ) := h n
      _ ≤ C * ρ^n * (n : ℝ)^n := mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = C * (ρ * (n : ℝ))^n := by rw [mul_pow, mul_assoc]
      _ ≤ C * (ω / 2)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsmall _) hC
      _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring
  have hx : A ≤ C * (1 / 2 : ℝ)^n := le_of_mul_le_mul_left hstep (pow_pos hpos _)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (1 / 2 : ℝ)^n = Real.exp (-(n : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div, inv_pow]
  have he : -(n : ℝ) * Real.log 2 ≤ Real.log 2 - q * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right hq.le hlog.le
    linarith
  calc
    A ≤ C * (1 / 2 : ℝ)^n := hx
    _ = C * Real.exp (-(n : ℝ) * Real.log 2) := by rw [hpow]
    _ ≤ C * Real.exp (Real.log 2 - q * Real.log 2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hw : -(q * Real.log 2) = -(Real.log 2 / (2 * ρ)) * ω := by
        dsimp [q]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [hw]
      ring

end HeatGevreyFourierDecay

#print axioms HeatGevreyFourierDecay.exponential_bound
