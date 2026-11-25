import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section

namespace HeatAnalyticObservabilityTelescoping

open Filter
open scoped Topology

/-- The geometric time-grid argument in the analytic observability proof.
`E k` is the state norm at the left node and `Q k` is the integral of the
observation on its associated window. -/
theorem telescope (q d α C C₀ D O M : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hd : 0 < d)
    (hC : 0 ≤ C) (hD : 0 < D) (hweight : C₀ ≤ D * (1 - α * (q⁻¹ - 1)))
    (E Q : ℕ → ℝ) (hE₀ : ∀ n, 0 ≤ E n) (hE : ∀ n, E n ≤ M)
    (hQ₀ : ∀ n, 0 ≤ Q n) (hQ : ∀ n, ∑ k ∈ Finset.range n, Q k ≤ O)
    (hstep : ∀ n (ε : ℝ), 0 < ε → E n ≤ ε * E (n + 1) +
      C * ε ^ (-α) * Real.exp (C₀ / (d * q ^ n)) * Q n) :
    E 0 ≤ C * Real.exp (D / d) * O := by
  let δ := fun k : ℕ => d * q ^ k
  let w := fun k => Real.exp (-D / δ k)
  let γ := fun k => -D * (q⁻¹ - 1) / δ k
  have hδ (k : ℕ) : 0 < δ k := mul_pos hd (pow_pos hq k)
  have hδ_succ (k : ℕ) : δ (k + 1) = δ k * q := by simp only [δ, pow_succ, mul_assoc]
  have hrec (k : ℕ) : w k * Real.exp (γ k) = w (k + 1) := by
    dsimp only [w]
    rw [← Real.exp_add, hδ_succ]
    congr 1
    dsimp only [γ]
    field_simp [hq.ne', (hδ k).ne']
    ring
  have hcomp (k : ℕ) : w k * (Real.exp (γ k)) ^ (-α) * Real.exp (C₀ / δ k) ≤ 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    dsimp only [w, γ]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have he : -D / δ k + γ k * -α + C₀ / δ k =
        (C₀ - D * (1 - α * (q⁻¹ - 1))) / δ k := by
      dsimp only [γ]
      ring
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hweight) (hδ k).le
  have hlocal (k : ℕ) : w k * E k ≤ w (k + 1) * E (k + 1) + C * Q k := by
    have h := mul_le_mul_of_nonneg_left (hstep k (Real.exp (γ k)) (Real.exp_pos _))
      (Real.exp_pos (-D / δ k)).le
    change w k * E k ≤ w k * (Real.exp (γ k) * E (k + 1) +
      C * (Real.exp (γ k)) ^ (-α) * Real.exp (C₀ / δ k) * Q k) at h
    have he : w k * (Real.exp (γ k) * E (k + 1) +
        C * (Real.exp (γ k)) ^ (-α) * Real.exp (C₀ / δ k) * Q k) =
        w (k + 1) * E (k + 1) + (C * Q k) *
          (w k * (Real.exp (γ k)) ^ (-α) * Real.exp (C₀ / δ k)) := by
      rw [← hrec k]
      ring
    rw [he] at h
    exact h.trans (add_le_add le_rfl (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcomp k) (mul_nonneg hC (hQ₀ k))))
  have hsum (n : ℕ) : w 0 * E 0 ≤ w n * E n + C * ∑ k ∈ Finset.range n, Q k := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hlocal n]
  have hlimw : Tendsto w atTop (𝓝 0) := by
    have hi : 1 < q⁻¹ := (one_lt_inv₀ hq).mpr hq₁
    have hneg : -D / d < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hD) hd
    have hl := Real.tendsto_exp_atBot.comp ((tendsto_pow_atTop_atTop_of_one_lt hi).const_mul_atTop_of_neg hneg)
    have he (k : ℕ) : -D / d * (q⁻¹)^k = -D / δ k := by
      dsimp only [δ]
      simp only [inv_pow, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    simpa only [Function.comp_def, he] using hl
  have hlast : Tendsto (fun n => w n * E n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => w n * M) atTop (𝓝 0) by simpa using hlimw.mul_const M)
    · intro n
      exact mul_nonneg (Real.exp_pos _).le (hE₀ n)
    · intro n
      exact mul_le_mul_of_nonneg_left (hE n) (Real.exp_pos _).le
  have hb : w 0 * E 0 ≤ C * O := by
    have hl : Tendsto (fun n => w n * E n + C * O) atTop (𝓝 (C * O)) := by
      simpa only [zero_add] using hlast.add_const (C * O)
    apply ge_of_tendsto hl
    exact Eventually.of_forall fun n => (hsum n).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hQ n) hC))
  have hw₀ : w 0 = Real.exp (-D / d) := by simp [w, δ]
  have h := mul_le_mul_of_nonneg_left hb (Real.exp_pos (D / d)).le
  rw [hw₀, ← mul_assoc, ← Real.exp_add, show D / d + -D / d = 0 by ring,
    Real.exp_zero, one_mul] at h
  calc
    _ ≤ Real.exp (D / d) * (C * O) := h
    _ = _ := by ring

end HeatAnalyticObservabilityTelescoping

#print axioms HeatAnalyticObservabilityTelescoping.telescope
