import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section

namespace HeatAnalyticInterpolationBalance

open Filter
open scoped Topology

/-- Balancing the growth of the interpolation coefficients against the
geometric decay of the remainder gives a square-root observation bound. -/
theorem sqrt_bound {A M ε q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hcap : A ≤ M) (hsteps : ∀ n : ℕ, 1 ≤ n → A ≤ ε / q ^ n + M * q ^ n) :
    A ≤ (1 + q⁻¹) * Real.sqrt (M * ε) := by
  have hconv : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq₁
  have hc : 1 ≤ 1 + q⁻¹ := by have := inv_nonneg.mpr hq.le; linarith
  by_cases hM0 : M = 0
  · simpa [hM0] using hcap
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  by_cases hε0 : ε = 0
  · have hb (n : ℕ) (hn : 1 ≤ n) : A ≤ M * q ^ n := by simpa [hε0] using hsteps n hn
    have hlim : Tendsto (fun n : ℕ => M * q ^ n) atTop (𝓝 0) := by
      simpa using hconv.const_mul M
    have hA := ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun n hn => hb n hn)
    simpa [hε0] using hA
  have hεp : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
  let s := Real.sqrt (ε / M)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hεp hMp)
  have hs2 : s ^ 2 * M = ε := by
    rw [Real.sq_sqrt (div_nonneg hε hM), div_mul_cancel₀ _ hM0]
  have hsM : Real.sqrt (M * ε) = M * s :=
    (Real.sqrt_eq_iff_eq_sq (mul_nonneg hM hε) (mul_nonneg hM hs.le)).mpr (by
      calc M * ε = M * (s ^ 2 * M) := congrArg (M * ·) hs2.symm
        _ = (M * s) ^ 2 := by ring)
  rw [hsM]
  by_cases hs1 : 1 ≤ s
  · calc
      A ≤ M := hcap
      _ ≤ M * s := le_mul_of_one_le_right hM hs1
      _ ≤ (1 + q⁻¹) * (M * s) := le_mul_of_one_le_left (by positivity) hc
  have hex : ∃ n : ℕ, q ^ n ≤ s :=
    ((hconv.eventually_lt_const hs).mono fun _ h => h.le).exists
  let n := Nat.find hex
  have hlo : q ^ n ≤ s := Nat.find_spec hex
  have hn : 1 ≤ n := by
    have hz : n ≠ 0 := fun h0 => hs1 (by simpa [h0] using hlo)
    omega
  have hprec : s < q ^ (n - 1) := lt_of_not_ge (Nat.find_min hex (by omega))
  have hhi : s * q ≤ q ^ n := by
    have ht := mul_le_mul_of_nonneg_right hprec.le hq.le
    rwa [← pow_succ, show n - 1 + 1 = n by omega] at ht
  have hratio : ε / q ^ n ≤ q⁻¹ * (M * s) := by
    rw [div_le_iff₀ (pow_pos hq n), ← hs2]
    calc
      s ^ 2 * M = (q⁻¹ * (M * s)) * (s * q) := by field_simp
      _ ≤ (q⁻¹ * (M * s)) * q ^ n := mul_le_mul_of_nonneg_left hhi (by positivity)
  calc
    A ≤ ε / q ^ n + M * q ^ n := hsteps _ hn
    _ ≤ q⁻¹ * (M * s) + M * s := add_le_add hratio (mul_le_mul_of_nonneg_left hlo hM)
    _ = (1 + q⁻¹) * (M * s) := by ring

end HeatAnalyticInterpolationBalance

#print axioms HeatAnalyticInterpolationBalance.sqrt_bound
