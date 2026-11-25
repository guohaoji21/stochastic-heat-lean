import HeatTorusAxisFourier
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section

namespace HeatGevreyFourierExtension

open Complex Set UnitAddTorus
open HeatTorusGaussian (wrap)

variable {ι : Type*} [Fintype ι]

/-- The frequency weight for a finite lattice of Fourier modes. -/
def weight (k : ι → ℤ) : ℝ := ∑ i, |(k i : ℝ)|

theorem weight_nonneg (k : ι → ℤ) : 0 ≤ weight k := Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem summable_exp_abs {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-a * |(n : ℝ)|)) := by
  have hg := summable_geometric_of_lt_one (Real.exp_pos (-a)).le (Real.exp_lt_one_iff.mpr (by linarith))
  have hn : Summable (fun n : ℕ => Real.exp (-a * (n : ℝ))) := by
    simpa only [← Real.exp_nat_mul, mul_comm] using hg
  have habs (n : ℕ) : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast, habs] using hn
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, habs] using hn

private theorem summable_fin_exp_weight {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Summable (fun k : Fin n → ℤ => Real.exp (-a * weight k)) := by
  induction n with
  | zero =>
    letI : Fintype (Fin 0 → ℤ) := Fintype.ofSubsingleton (fun j => Fin.elim0 j)
    exact (hasSum_fintype _).summable
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    apply e.summable_iff.mp
    convert (summable_exp_abs ha).mul_of_nonneg ih (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le) using 1
    funext p
    simp only [Function.comp_apply, weight, Fin.sum_univ_succ, e, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ, mul_add, Real.exp_add]

theorem summable_exp_weight {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ι → ℤ => Real.exp (-a * weight k)) := by
  let e := Fintype.equivFin ι
  let E : (Fin (Fintype.card ι) → ℤ) ≃ (ι → ℤ) := (Equiv.piCongrLeft (fun _ => ℤ) e).symm
  apply E.summable_iff.mp
  convert summable_fin_exp_weight ha (Fintype.card ι) using 1
  funext k
  have h : weight (E k) = weight k := by
    unfold weight
    simp only [E, Equiv.piCongrLeft_symm_apply]
    exact e.sum_comp fun i => |(k i : ℝ)|
  rw [Function.comp_apply, h]

/-- The complex domain with coordinatewise imaginary parts of magnitude less than `r`. -/
def tube (r : ℝ) : Set (ι → ℂ) := ⋂ i, (fun z : ι → ℂ => (z i).im) ⁻¹' Ioo (-r) r

theorem isOpen_tube (r : ℝ) : IsOpen (tube (ι := ι) r) :=
  isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_im.comp (continuous_apply i))

private theorem convex_tube (r : ℝ) : Convex ℝ (tube (ι := ι) r) := by
  apply convex_iInter
  intro i
  exact (convex_Ioo (-r) r).linear_preimage
    (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i)).toLinearMap

private def phase (k : ι → ℤ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (2 * Real.pi * I * k i : ℂ) • ContinuousLinearMap.proj i

private theorem phase_apply (k : ι → ℤ) (z : ι → ℂ) :
    phase k z = ∑ i, (2 * Real.pi * I * k i : ℂ) * z i := by
  simp [phase, ContinuousLinearMap.sum_apply, smul_eq_mul]

private theorem norm_factor (n : ℤ) : ‖(2 * Real.pi * I * n : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| := by
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast]

private theorem phase_norm (k : ι → ℤ) : ‖phase k‖ ≤ 2 * Real.pi * weight k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [weight_nonneg k])
  intro z
  rw [phase_apply]
  calc
    _ ≤ ∑ i, ‖(2 * Real.pi * I * k i : ℂ) * z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (2 * Real.pi * |(k i : ℝ)|) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_factor]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (by positivity)
    _ = _ := by rw [weight, Finset.mul_sum, Finset.sum_mul]

private theorem phase_re_le (k : ι → ℤ) (r : ℝ) (z : ι → ℂ) (hz : z ∈ tube r) :
    (phase k z).re ≤ (2 * Real.pi * r) * weight k := by
  have hz' (i : ι) : |(z i).im| ≤ r := (abs_lt.mpr (mem_iInter.mp hz i)).le
  rw [phase_apply, show (∑ i, (2 * Real.pi * I * k i : ℂ) * z i).re =
      ∑ i, ((2 * Real.pi * I * k i : ℂ) * z i).re from map_sum reCLM _ _, weight, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : ((2 * Real.pi * I * k i : ℂ) * z i).re = -(2 * Real.pi * ((k i : ℝ) * (z i).im)) := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [he]
  calc
    _ ≤ 2 * Real.pi * |(k i : ℝ) * (z i).im| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
    _ ≤ 2 * Real.pi * (|(k i : ℝ)| * r) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hz' i) (abs_nonneg _)) (by positivity)
    _ = _ := by ring

private theorem character_real (k : ι → ℤ) (x : ι → ℝ) :
    Complex.exp (phase k (fun i => (x i : ℂ))) = mFourier k (wrap x) := by
  rw [phase_apply, Complex.exp_sum]
  unfold mFourier
  apply Finset.prod_congr rfl
  intro i _
  simp only [wrap, fourier_coe_apply, Complex.ofReal_one, div_one]

private theorem character_period (k v : ι → ℤ) (z : ι → ℂ) :
    Complex.exp (phase k (z + fun i => (v i : ℂ))) = Complex.exp (phase k z) := by
  rw [map_add, Complex.exp_add]
  have hs : phase k (fun i => (v i : ℂ)) = (↑(∑ i, k i * v i) : ℂ) * (2 * Real.pi * I) := by
    rw [phase_apply]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, exp_int_mul_two_pi_mul_I, mul_one]

/-- A Banach-valued Fourier series with exponentially decaying coefficients
extends to a periodic holomorphic function with a uniform tube bound. -/
theorem exists_series_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (c : (ι → ℤ) → E) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (hdec : ∀ k, ‖c k‖ ≤ C * Real.exp (-a * weight k)) :
    ∃ F : (ι → ℂ) → E, DifferentiableOn ℂ F (tube (a / (4 * Real.pi))) ∧
      (∀ x : ι → ℝ, F (fun i => (x i : ℂ)) = ∑' k, (mFourier k (wrap x)) • c k) ∧
      (∀ (z : ι → ℂ) (v : ι → ℤ), F (z + fun i => (v i : ℂ)) = F z) ∧
      (∀ z ∈ tube (a / (4 * Real.pi)), ‖F z‖ ≤ ∑' k : ι → ℤ, C * Real.exp (-(a / 2) * weight k)) := by
  let term (k : ι → ℤ) (z : ι → ℂ) := Complex.exp (phase k z) • c k
  have term_deriv (k : ι → ℤ) (z : ι → ℂ) :
      HasFDerivAt (term k) ((phase k).smulRight (term k z)) z := by
    have hd := (Complex.hasDerivAt_exp (phase k z)).comp_hasFDerivAt z (phase k).hasFDerivAt
    have heq : (Complex.exp (phase k z) • phase k).smulRight (c k) =
        (phase k).smulRight (term k z) := by
      ext w
      change (Complex.exp (phase k z) * phase k w) • c k = phase k w • (Complex.exp (phase k z) • c k)
      rw [smul_smul, mul_comm]
    rw [← heq]
    exact hd.smul_const (c k)
  let r := a / (4 * Real.pi)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr' : 2 * Real.pi * r = a / 2 := by dsimp [r]; field_simp; ring
  let u₀ := fun k : ι → ℤ => C * Real.exp (-(a / 2) * weight k)
  let u₁ := fun k : ι → ℤ => (C * (2 * Real.pi) / (a / 4)) * Real.exp (-(a / 4) * weight k)
  have hu₀ : Summable u₀ := (summable_exp_weight (show 0 < a / 2 by positivity)).mul_left C
  have hu₁ : Summable u₁ :=
    (summable_exp_weight (show 0 < a / 4 by positivity)).mul_left (C * (2 * Real.pi) / (a / 4))
  have ht (k : ι → ℤ) (z : ι → ℂ) (hz : z ∈ tube r) : ‖term k z‖ ≤ u₀ k := by
    have hrz := phase_re_le k r z hz
    rw [hr'] at hrz
    change ‖Complex.exp (phase k z) • c k‖ ≤ u₀ k
    rw [norm_smul, Complex.norm_exp, mul_comm]
    calc
      _ ≤ (C * Real.exp (-a * weight k)) * Real.exp (a / 2 * weight k) :=
        mul_le_mul (hdec k) (Real.exp_le_exp.mpr hrz) (Real.exp_pos _).le (by positivity)
      _ = _ := by
        dsimp only [u₀]
        rw [mul_assoc, ← Real.exp_add]
        congr 2 <;> ring
  have hd (k : ι → ℤ) (z : ι → ℂ) (hz : z ∈ tube r) :
      ‖(phase k).smulRight (term k z)‖ ≤ u₁ k := by
    rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm]
    have hw := weight_nonneg k
    have he : weight k ≤ Real.exp (a / 4 * weight k) / (a / 4) := by
      apply (le_div_iff₀ (by positivity : 0 < a / 4)).mpr
      have h := Real.add_one_le_exp (a / 4 * weight k)
      linarith
    calc
      _ ≤ u₀ k * ((2 * Real.pi) * weight k) :=
        mul_le_mul (ht k z hz) (phase_norm k) (norm_nonneg _) (by dsimp [u₀]; positivity)
      _ ≤ u₀ k * ((2 * Real.pi) * (Real.exp (a / 4 * weight k) / (a / 4))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by dsimp [u₀]; positivity)
      _ = u₁ k := by
        dsimp [u₀, u₁]
        rw [div_eq_mul_inv, div_eq_mul_inv, ← show -(a / 2) * weight k + a / 4 * weight k =
          -(a / 4) * weight k by ring, Real.exp_add]
        ring
  let F := fun z => ∑' k, term k z
  have hz₀ : (0 : ι → ℂ) ∈ tube r := by
    apply mem_iInter.mpr
    intro i
    exact ⟨by simpa using neg_lt_zero.mpr hr, by simpa using hr⟩
  have hsum₀ : Summable (fun k => term k 0) := Summable.of_norm_bounded hu₀ fun k => ht k 0 hz₀
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hasFDerivAt_tsum_of_isPreconnected hu₁ (isOpen_tube r) (convex_tube r).isPreconnected
      (fun k z _ => term_deriv k z) hd hz₀ hsum₀ hz).differentiableAt.differentiableWithinAt
  · intro x
    exact tsum_congr (fun k => congrArg (fun s : ℂ => s • c k) (character_real k x))
  · intro z v
    exact tsum_congr (fun k => congrArg (fun s : ℂ => s • c k) (character_period k v z))
  · intro z hz
    exact tsum_of_norm_bounded hu₀.hasSum (fun k => ht k z hz)

/-- Uniform bounds on finite weighted energy sums give a holomorphic
extension with a tube bound linear in the square root of that energy. -/
theorem exists_energy_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (c : (ι → ℤ) → E) (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (hcap : ∀ S : Finset (ι → ℤ), ∑ k ∈ S, Real.exp (2 * a * weight k) * ‖c k‖ ^ 2 ≤ M ^ 2) :
    ∃ F : (ι → ℂ) → E, DifferentiableOn ℂ F (tube (a / (4 * Real.pi))) ∧
      (∀ x : ι → ℝ, F (fun i => (x i : ℂ)) = ∑' k, (mFourier k (wrap x)) • c k) ∧
      (∀ (z : ι → ℂ) (v : ι → ℤ), F (z + fun i => (v i : ℂ)) = F z) ∧
      (∀ z ∈ tube (a / (4 * Real.pi)), ‖F z‖ ≤ M * (∑' k : ι → ℤ, Real.exp (-(a / 2) * weight k))) := by
  have hdec (k : ι → ℤ) : ‖c k‖ ≤ M * Real.exp (-a * weight k) := by
    classical
    have h := hcap {k}
    rw [Finset.sum_singleton] at h
    have hsq : (‖c k‖ * Real.exp (a * weight k)) ^ 2 ≤ M ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, ← mul_assoc, mul_comm]
      exact h
    have hle := (sq_le_sq₀ (by positivity) hM).mp hsq
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).mpr hle
  obtain ⟨F, hF, hreal, hper, hf⟩ := exists_series_extension c M a hM ha hdec
  exact ⟨F, hF, hreal, hper, fun z hz => by simpa only [tsum_mul_left] using hf z hz⟩

/-- Exponential Fourier decay supplies a bounded holomorphic extension of a
continuous scalar function on the torus. -/
theorem exists_extension (b : C(UnitAddTorus ι, ℂ)) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (hdec : ∀ k : ι → ℤ, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-a * weight k)) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F (tube r) ∧
      (∀ x : ι → ℝ, F (fun i => (x i : ℂ)) = b (wrap x)) ∧
      (∀ (z : ι → ℂ) (v : ι → ℤ), F (z + fun i => (v i : ℂ)) = F z) ∧
      ∃ B : ℝ, ∀ z ∈ tube r, ‖F z‖ ≤ B := by
  obtain ⟨F, hF, hreal, hper, hbound⟩ := exists_series_extension (mFourierCoeff b) C a hC ha hdec
  refine ⟨a / (4 * Real.pi), by positivity, F, hF, ?_, hper, _, hbound⟩
  intro x
  rw [hreal]
  have hc : Summable (mFourierCoeff b) :=
    Summable.of_norm_bounded ((summable_exp_weight ha).mul_left C) hdec
  simpa only [smul_eq_mul, mul_comm] using (hasSum_mFourier_series_apply_of_summable hc (wrap x)).tsum_eq

end HeatGevreyFourierExtension

#print axioms HeatGevreyFourierExtension.exists_series_extension
#print axioms HeatGevreyFourierExtension.exists_energy_extension
#print axioms HeatGevreyFourierExtension.exists_extension
