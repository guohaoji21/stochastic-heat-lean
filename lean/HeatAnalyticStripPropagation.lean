import HeatAnalyticLocalPropagation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

namespace HeatAnalyticStripPropagation

open Metric Set

def strip (ρ : ℝ) : Set ℂ := {z | |z.im| < ρ}

private theorem extend_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {ρ r M B R : ℝ} (hr : 0 < r) (hρ : 100 * r < ρ) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hf : DifferentiableOn ℂ f (strip ρ))
    (hcap : ∀ z ∈ strip ρ, ‖f z‖ ≤ M) (hsmall : ∀ y : ℝ, |y| ≤ R + r → ‖f y‖ ≤ B)
    (x : ℝ) (hx : |x| ≤ R + 2 * r) : ‖f x‖ ≤ 17 * Real.sqrt (M * B) := by
  let y := max (-R) (min x R)
  have hy : |y| ≤ R := abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hxy : |x - y| ≤ 2 * r := by
    dsimp only [y]
    rcases abs_le.mp hx with ⟨hlo, hhi⟩
    rcases le_total x R with hxR | hxR
    · rcases le_total x (-R) with hxL | hxL
      · rw [min_eq_left hxR, max_eq_left hxL]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [min_eq_left hxR, max_eq_right hxL, sub_self, abs_zero]
        positivity
    · rw [min_eq_right hxR, max_eq_right (by linarith : -R ≤ R)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsub : closedBall (y : ℂ) (100 * r) ⊆ strip ρ := by
    intro z hz
    have h := Complex.abs_im_le_norm (z - y)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    have hz' : ‖z - (y : ℂ)‖ ≤ 100 * r := by simpa only [dist_eq_norm] using mem_closedBall.mp hz
    exact (h.trans hz').trans_lt hρ
  exact HeatAnalyticLocalPropagation.segment_to_disk hr hM hB (hf.mono hsub)
    (fun z hz => hcap z (hsub hz)) (fun t ht => by
      rw [← Complex.ofReal_add]
      apply hsmall
      exact (abs_add_le y t).trans (add_le_add hy ht)) (by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hxy)

private theorem bound_step {M q : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) (k : ℕ) :
    17 * Real.sqrt (M * (289 * M * q ^ ((1 / 2 : ℝ) ^ k))) =
      289 * M * q ^ ((1 / 2 : ℝ) ^ (k + 1)) := by
  have he : Real.sqrt (q ^ ((1 / 2 : ℝ) ^ k)) = q ^ ((1 / 2 : ℝ) ^ (k + 1)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq, pow_succ]
  calc
    _ = 17 * Real.sqrt ((17 * M) ^ 2 * q ^ ((1 / 2 : ℝ) ^ k)) := by congr 2; ring
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), he]; ring

/-- Iterate real-segment propagation along an entire strip. The exponent
depends only on the number of intervals crossed. -/
theorem segment_to_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {ρ r M ε : ℝ} (hr : 0 < r) (hρ : 100 * r < ρ) (hM : 0 < M) (hε : 0 ≤ ε)
    (hf : DifferentiableOn ℂ f (strip ρ)) (hcap : ∀ z ∈ strip ρ, ‖f z‖ ≤ M)
    (hsmall : ∀ x : ℝ, |x| ≤ r → ‖f x‖ ≤ ε) (k : ℕ) (x : ℝ) (hx : |x| ≤ (k + 1 : ℝ) * r) :
    ‖f x‖ ≤ 289 * M * (ε / M) ^ ((1 / 2 : ℝ) ^ k) := by
  induction k generalizing x with
  | zero =>
    simp only [Nat.cast_zero, zero_add, one_mul] at hx
    calc
      _ ≤ ε := hsmall x hx
      _ ≤ 289 * ε := le_mul_of_one_le_left hε (by norm_num)
      _ = _ := by
        rw [pow_zero, Real.rpow_one]
        field_simp
  | succ k ih =>
    have hq : 0 ≤ ε / M := div_nonneg hε hM.le
    have hB : 0 ≤ 289 * M * (ε / M) ^ ((1 / 2 : ℝ) ^ k) := by positivity
    have hs (t : ℝ) (ht : |t| ≤ (k : ℝ) * r + r) :
        ‖f t‖ ≤ 289 * M * (ε / M) ^ ((1 / 2 : ℝ) ^ k) := ih t (by linarith)
    have hx' : |x| ≤ (k : ℝ) * r + 2 * r := by
      push_cast at hx
      linarith
    exact (extend_interval hr hρ (by positivity : 0 ≤ (k : ℝ) * r) hM.le hB hf hcap hs x hx').trans_eq
      (bound_step hM.le hq k)

end HeatAnalyticStripPropagation

#print axioms HeatAnalyticStripPropagation.segment_to_interval
