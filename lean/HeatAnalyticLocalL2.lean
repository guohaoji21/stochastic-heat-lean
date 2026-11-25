import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace HeatAnalyticLocalL2

open MeasureTheory Metric Set
open scoped ENNReal

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- A uniform bound and a Lipschitz bound convert the squared integral on
a box into a pointwise bound on the concentric box of half its radius. -/
theorem norm_le_of_local_energy (f : (ι → ℝ) → E) (c x : ι → ℝ) {r M L A : ℝ}
    (hr : 0 < r) (hM : 0 < M) (hL : 0 ≤ L) (hscale : 2 * L * r ≤ M) (hA : 0 ≤ A)
    (hx : x ∈ closedBall c r) (hcap : ‖f x‖ ≤ M)
    (hlip : ∀ y, ‖f x - f y‖ ≤ L * ‖x - y‖)
    (henergy : (∫⁻ y in ball c (2 * r), ENNReal.ofReal (‖f y‖ ^ 2)) ≤ ENNReal.ofReal A) :
    ‖f x‖ ≤ M * (4 * A / (M ^ 2 * (2 * r) ^ Fintype.card ι)) ^
      ((↑(Fintype.card ι + 2) : ℝ)⁻¹) := by
  let d := Fintype.card ι
  let u := ‖f x‖ / M
  have hu : 0 ≤ u := div_nonneg (norm_nonneg _) hM.le
  have hu1 : u ≤ 1 := (div_le_one₀ hM).mpr hcap
  let δ := r * u
  have huF : M * u = ‖f x‖ := by
    dsimp only [u]
    rw [mul_comm, div_mul_cancel₀ _ hM.ne']
  have hZ : 0 ≤ 4 * A / (M ^ 2 * (2 * r) ^ d) := by positivity
  by_cases huz : u = 0
  · rw [← huF, huz, mul_zero]
    positivity
  have hδ : 0 < δ := mul_pos hr (lt_of_le_of_ne hu (Ne.symm huz))
  have hδr : δ ≤ r := mul_le_of_le_one_right hr.le hu1
  have hsub : ball x δ ⊆ ball c (2 * r) := by
    intro y hy
    have H := (dist_triangle y x c).trans_lt
      (add_lt_add_of_lt_of_le (mem_ball.mp hy) (mem_closedBall.mp hx))
    exact mem_ball.mpr (H.trans_le (by linarith))
  have hheight {y : ι → ℝ} (hy : y ∈ ball x δ) : ‖f x‖ / 2 ≤ ‖f y‖ := by
    have hd : ‖x - y‖ ≤ δ := by simpa only [dist_comm y x, dist_eq_norm] using (mem_ball.mp hy).le
    have hb : L * δ ≤ ‖f x‖ / 2 := by
      have hh := mul_le_mul_of_nonneg_right hscale hu
      dsimp only [δ]
      rw [← huF]
      linarith only [show 2 * (L * (r * u)) ≤ M * u by convert hh using 1 <;> ring]
    have htri := norm_add_le (f x - f y) (f y)
    rw [sub_add_cancel] at htri
    have hfxy := (hlip y).trans ((mul_le_mul_of_nonneg_left hd hL).trans hb)
    linarith
  have hm : (∫⁻ y in ball x δ, ENNReal.ofReal ((‖f x‖ / 2) ^ 2)) ≤
      ∫⁻ y in ball x δ, ENNReal.ofReal (‖f y‖ ^ 2) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (hheight hy) 2)
  have hm' := hm.trans ((lintegral_mono_set hsub).trans henergy)
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_pi_ball x hδ,
    ← ENNReal.ofReal_mul (by positivity)] at hm'
  have hpow_bound : (‖f x‖ / 2) ^ 2 * (2 * δ) ^ d ≤ A :=
    (ENNReal.ofReal_le_ofReal_iff hA).mp hm'
  have heq : (‖f x‖ / 2) ^ 2 * (2 * δ) ^ d = (M ^ 2 * (2 * r) ^ d / 4) * u ^ (d + 2) := by
    rw [← huF, show 2 * δ = (2 * r) * u by dsimp [δ]; ring, mul_pow (2 * r) u, pow_add]
    ring
  have hden : 0 < M ^ 2 * (2 * r) ^ d := by positivity
  have hpow : u ^ (d + 2) ≤ 4 * A / (M ^ 2 * (2 * r) ^ d) := by
    rw [le_div_iff₀ hden]
    rw [heq] at hpow_bound
    linarith only [show u ^ (d + 2) * (M ^ 2 * (2 * r) ^ d) / 4 ≤ A by convert hpow_bound using 1 <;> ring]
  have hn : (↑(d + 2) : ℝ) ≠ 0 := by positivity
  have hroot := Real.rpow_le_rpow (pow_nonneg hu _) hpow
    (by positivity : 0 ≤ (↑(d + 2) : ℝ)⁻¹)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu, mul_inv_cancel₀ hn, Real.rpow_one] at hroot
  exact huF ▸ mul_le_mul_of_nonneg_left hroot hM.le

end HeatAnalyticLocalL2

#print axioms HeatAnalyticLocalL2.norm_le_of_local_energy
