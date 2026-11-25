import HeatAnalyticGalerkinEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace HeatGalerkinWeightedDrift

open HeatGevreyFourierExtension (weight weight_nonneg summable_exp_weight)
open HeatAnalyticGalerkinEnergy (translationWeight)
open HeatTorusFourier (frequencySquared)

variable {ι : Type*} [Fintype ι]

def translated (q : ι → ℝ) (b : (ι → ℤ) → ℂ) (k : ι → ℤ) : ℂ :=
  (translationWeight q k : ℂ) * b k

/-- A common row and column bound for all Galerkin truncations and all imaginary
translations in the smaller tube. -/
def coefficientBound (ι : Type*) [Fintype ι] (C a : ℝ) : ℝ :=
  1 + ∑' k : ι → ℤ, C * Real.exp (-(a / 2) * weight k)

theorem coefficientBound_pos {C a : ℝ} (hC : 0 ≤ C) : 0 < coefficientBound ι C a := by
  unfold coefficientBound
  exact add_pos_of_pos_of_nonneg one_pos (tsum_nonneg (fun _ => mul_nonneg hC (Real.exp_nonneg _)))

private theorem translated_norm_le {C a : ℝ}
    (b : (ι → ℤ) → ℂ) (hdec : ∀ k, ‖b k‖ ≤ C * Real.exp (-a * weight k))
    (q : ι → ℝ) (hq : ∀ i, |q i| ≤ a / 2) (k : ι → ℤ) :
    ‖translated q b k‖ ≤ C * Real.exp (-(a / 2) * weight k) := by
  have hθ : ∑ i, q i * (k i : ℝ) ≤ (a / 2) * weight k := by
    rw [weight, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hq i) (abs_nonneg _))
  rw [translated, norm_mul, Complex.norm_real, Real.norm_eq_abs, translationWeight,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp ((a / 2) * weight k) * (C * Real.exp (-a * weight k)) :=
      mul_le_mul (Real.exp_le_exp.mpr hθ) (hdec k) (norm_nonneg _) (Real.exp_nonneg _)
    _ = C * Real.exp (-(a / 2) * weight k) := by
      rw [mul_left_comm, ← Real.exp_add, show (a / 2) * weight k + -a * weight k =
        -(a / 2) * weight k by ring]

private theorem sum_bound {κ : Type*} [Fintype κ] {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (b : (ι → ℤ) → ℂ) (hdec : ∀ k, ‖b k‖ ≤ C * Real.exp (-a * weight k))
    (q : ι → ℝ) (hq : ∀ i, |q i| ≤ a / 2) (f : κ → (ι → ℤ)) (hf : Function.Injective f) :
    ∑ k, ‖translated q b (f k)‖ ≤ coefficientBound ι C a := by
  classical
  let m := fun k : ι → ℤ => C * Real.exp (-(a / 2) * weight k)
  let e : κ ↪ (ι → ℤ) := ⟨f, hf⟩
  have hm (k : ι → ℤ) : 0 ≤ m k := mul_nonneg hC (Real.exp_nonneg _)
  have hsm : Summable m := (summable_exp_weight (show 0 < a / 2 by positivity)).mul_left C
  calc
    _ ≤ ∑ k, m (f k) := Finset.sum_le_sum (fun k _ => translated_norm_le b hdec q hq (f k))
    _ = ∑ k ∈ Finset.univ.map e, m k := by simp [e]
    _ ≤ ∑' k, m k := hsm.sum_le_tsum _ (fun k _ => hm k)
    _ ≤ _ := le_add_of_nonneg_left zero_le_one

private theorem two_mul_re_le {β : ℝ} (hβ : 0 < β) (m x y : ℂ) :
    β * (2 * ((m * y) * star x).re) ≤ ‖m‖ * (β ^ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h₁ : ((m * y) * star x).re ≤ ‖m‖ * ‖y‖ * ‖x‖ := by
    simpa only [norm_mul, norm_star] using Complex.re_le_norm ((m * y) * star x)
  have h₂ : 2 * β * ‖y‖ * ‖x‖ ≤ β ^ 2 * ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (β * ‖x‖ - ‖y‖)]
  calc
    _ ≤ β * (2 * (‖m‖ * ‖y‖ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₁ (by norm_num)) hβ.le
    _ = ‖m‖ * (2 * β * ‖y‖ * ‖x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)

/-- Finite row and column sums control the real energy pairing. The constant
comes from the full Fourier series, independent of the finite frequency set. -/
theorem pairing_le {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (b : (ι → ℤ) → ℂ) (hdec : ∀ k, ‖b k‖ ≤ C * Real.exp (-a * weight k))
    (q : ι → ℝ) (hq : ∀ i, |q i| ≤ a / 2) (S : Finset (ι → ℤ)) (x y : ↥S → ℂ) :
    2 * (∑ k, ((∑ l, translated q b (k.val - l.val) * y l) * star (x k)).re) ≤
      (coefficientBound ι C a) ^ 2 * (∑ k, ‖x k‖ ^ 2) + ∑ k, ‖y k‖ ^ 2 := by
  let m (k l : ↥S) := translated q b (k.val - l.val)
  let β := coefficientBound ι C a
  have hβ : 0 < β := coefficientBound_pos hC
  have hrow (k : ↥S) : ∑ l, ‖m k l‖ ≤ β :=
    sum_bound hC ha b hdec q hq (fun l : ↥S => k.val - l.val)
      (fun j l h => Subtype.ext (sub_right_injective h))
  have hcol (l : ↥S) : ∑ k, ‖m k l‖ ≤ β :=
    sum_bound hC ha b hdec q hq (fun k : ↥S => k.val - l.val)
      (fun j k h => Subtype.ext (sub_left_injective h))
  change 2 * (∑ k, ((∑ l, m k l * y l) * star (x k)).re) ≤ _
  apply (mul_le_mul_iff_right₀ hβ).mp
  calc
    _ = ∑ k, ∑ l, β * (2 * ((m k l * y l) * star (x k)).re) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show (∑ l, m k l * y l * star (x k)).re =
        ∑ l, (m k l * y l * star (x k)).re from map_sum Complex.reCLM _ _]
      simp only [Finset.mul_sum]
    _ ≤ ∑ k, ∑ l, ‖m k l‖ * (β ^ 2 * ‖x k‖ ^ 2 + ‖y l‖ ^ 2) :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => two_mul_re_le hβ (m k l) (x k) (y l)))
    _ = (∑ k, (∑ l, ‖m k l‖) * (β ^ 2 * ‖x k‖ ^ 2)) +
        ∑ l, (∑ k, ‖m k l‖) * ‖y l‖ ^ 2 := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ (∑ k, β * (β ^ 2 * ‖x k‖ ^ 2)) + ∑ l, β * ‖y l‖ ^ 2 :=
      add_le_add (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hrow k) (by positivity))
        (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hcol l) (sq_nonneg _))
    _ = _ := by simp only [Finset.mul_sum, mul_add, β]

/-- The scalar correction for an affine imaginary translation, including the
noise coupling bound. -/
def compensation (P : ℝ) (v : ι → ℝ) (β : ℝ) : ℝ :=
  β ^ 2 + ∑ i, (v i / (2 * Real.pi / P)) ^ 2 / 2

theorem diagonal_lower {P : ℝ} (hP : 0 < P) (v : ι → ℝ) (k : ι → ℤ) (β : ℝ) :
    β ^ 2 ≤ 2 * frequencySquared P k + 2 * (∑ i, v i * (k i : ℝ)) + compensation P v β := by
  let c := 2 * Real.pi / P
  have hc : c ≠ 0 := ne_of_gt (div_pos (by positivity) hP)
  have h (i : ι) : 0 ≤ 2 * (c ^ 2 * (k i : ℝ) ^ 2) +
      2 * (v i * (k i : ℝ)) + (v i / c) ^ 2 / 2 := by
    have he : 2 * (c ^ 2 * (k i : ℝ) ^ 2) + 2 * (v i * (k i : ℝ)) +
        (v i / c) ^ 2 / 2 = 2 * (c * (k i : ℝ) + v i / (2 * c)) ^ 2 := by
      field_simp [hc]
      ring
    rw [he]
    positivity
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  unfold frequencySquared compensation
  change 0 ≤ _ at hsum
  dsimp only [c] at hsum
  linarith

/-- The integrand of the compensated, directionally weighted energy is
nonnegative. This estimate is uniform across finite Galerkin spaces. -/
theorem energy_nonneg {P C a : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < a)
    (b : (ι → ℤ) → ℂ) (hdec : ∀ k, ‖b k‖ ≤ C * Real.exp (-a * weight k))
    (q v : ι → ℝ) (hq : ∀ i, |q i| ≤ a / 2) (S : Finset (ι → ℤ)) (x y : ↥S → ℂ) :
    0 ≤ ∑ k : ↥S, (
      (2 * frequencySquared P k.val + 2 * (∑ i, v i * (k.val i : ℝ)) +
        compensation P v (coefficientBound ι C a)) * ‖x k‖ ^ 2 +
      ‖y k‖ ^ 2 - 2 * ((∑ l, translated q b (k.val - l.val) * y l) * star (x k)).re) := by
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun (k : ↥S) _ =>
    mul_le_mul_of_nonneg_right (diagonal_lower hP v k.val (coefficientBound ι C a)) (sq_nonneg ‖x k‖))
  rw [← Finset.mul_sum] at hd
  have hc := pairing_le hC ha b hdec q hq S x y
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end HeatGalerkinWeightedDrift

#print axioms HeatGalerkinWeightedDrift.energy_nonneg
