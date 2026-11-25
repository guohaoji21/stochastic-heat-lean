import HeatGevreyFourierExtension
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace HeatAnalyticGalerkinEnergy

open MeasureTheory UnitAddTorus
open HeatGevreyFourierExtension (weight)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

/-- The exponential multiplier of an imaginary translation. -/
def translationWeight (q : ι → ℝ) (k : ι → ℤ) : ℝ :=
  Real.exp (∑ i, q i * (k i : ℝ))

theorem translationWeight_add (q : ι → ℝ) (k l : ι → ℤ) :
    translationWeight q (k + l) = translationWeight q k * translationWeight q l := by
  simp only [translationWeight, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib,
    Real.exp_add]

/-- After the Fourier translation, the finite convolution is the convolution
of the two individually translated coefficient arrays. -/
theorem translate_convolution (q : ι → ℝ) (S : Finset (ι → ℤ))
    (b y : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    (translationWeight q k : ℂ) * (∑ l ∈ S, b (k - l) * y l) =
      ∑ l ∈ S, ((translationWeight q (k - l) : ℂ) * b (k - l)) *
        ((translationWeight q l : ℂ) * y l) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have h := translationWeight_add q (k - l) l
  rw [sub_add_cancel] at h
  rw [h, Complex.ofReal_mul]
  ring

/-- The actual Haar Fourier coefficient of a continuous multiplier times a
Galerkin polynomial is the corresponding finite convolution. -/
theorem coefficient_mul_polynomial (b : C(UnitAddTorus ι, ℂ)) (S : Finset (ι → ℤ))
    (y : (ι → ℤ) → ℂ) (k : ι → ℤ) :
    mFourierCoeff (fun x => b x * ∑ l ∈ S, y l * mFourier l x) k =
      ∑ l ∈ S, mFourierCoeff b (k - l) * y l := by
  let g (l : ι → ℤ) (x : UnitAddTorus ι) := mFourier (-k) x * (b x * (y l * mFourier l x))
  have hgi (l : ι → ℤ) : Integrable (g l) volume := by
    have hg : Continuous (g l) := (mFourier (-k)).continuous.mul
      (b.continuous.mul (continuous_const.mul (mFourier l).continuous))
    exact hg.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hg (l : ι → ℤ) : (∫ x, g l x) = mFourierCoeff b (k - l) * y l := by
    rw [mFourierCoeff, ← integral_mul_const]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    have hm : mFourier (-(k - l)) x = mFourier (-k) x * mFourier l x := by
      rw [show -(k - l) = -k + l by abel, mFourier_add]
    simp only [g, hm, smul_eq_mul]
    ring
  calc
    _ = ∫ x, ∑ l ∈ S, g l x := by
      unfold mFourierCoeff
      simp only [smul_eq_mul, Finset.mul_sum, g]
    _ = ∑ l ∈ S, ∫ x, g l x := integral_finsetSum S (fun l _ => hgi l)
    _ = _ := Finset.sum_congr rfl (fun l _ => hg l)

private def signedDirection (ε : ι → Bool) (i : ι) : ℝ := if ε i then 1 else -1

/-- Summing the directional estimates over sign choices controls the joint
exponential Fourier weight appearing in the analytic adjoint estimate. -/
theorem weighted_energy_le_sum_signs [DecidableEq ι] (r : ℝ) (S : Finset (ι → ℤ)) (X : (ι → ℤ) → ℂ) :
    ∑ k ∈ S, Real.exp (2 * r * weight k) * ‖X k‖ ^ 2 ≤
      ∑ ε : ι → Bool, ∑ k ∈ S,
        Real.exp (2 * r * ∑ i, signedDirection ε i * (k i : ℝ)) * ‖X k‖ ^ 2 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k _
  let ε : ι → Bool := fun i => decide (0 ≤ k i)
  have hsign : (∑ i, signedDirection ε i * (k i : ℝ)) = weight k := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : 0 ≤ k i
    · simp [signedDirection, ε, h, abs_of_nonneg (by exact_mod_cast h : 0 ≤ (k i : ℝ))]
    · have hn : (k i : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge h))
      simp [signedDirection, ε, h, abs_of_nonpos hn]
  rw [← hsign]
  exact Finset.single_le_sum
    (s := (Finset.univ : Finset (ι → Bool)))
    (f := fun σ => Real.exp (2 * r * ∑ i, signedDirection σ i * (k i : ℝ)) * ‖X k‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ ε)

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Algebraic lower bound for the translated Galerkin energy drift. The
complex-valued system uses the real inner product obtained by restriction of
scalars. The coupling square uses the adjoint of the translated multiplier. -/
theorem translated_drift_lower (X Y : E) (D : ι → E) (q : ι → ℝ)
    (B : E →L[ℝ] E) (β : ℝ) (hβ : ‖B.adjoint X‖ ≤ β * ‖X‖) :
    0 ≤ (∑ i, (2 * ‖D i‖ ^ 2 + 2 * q i * inner ℝ (D i) X)) +
      ‖Y‖ ^ 2 - 2 * inner ℝ (B Y) X +
      ((∑ i, q i ^ 2 / 2) + β^2) * ‖X‖ ^ 2 := by
  have hD : (∑ i, (2 * ‖D i‖ ^ 2 + 2 * q i * inner ℝ (D i) X)) +
      (∑ i, q i ^ 2 / 2) * ‖X‖ ^ 2 = ∑ i, 2 * ‖D i + (q i / 2) • X‖ ^ 2 := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hY : ‖Y‖ ^ 2 - 2 * inner ℝ (B Y) X = ‖Y - B.adjoint X‖ ^ 2 - ‖B.adjoint X‖ ^ 2 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, norm_sub_sq_real]
    ring
  have hY' : ‖B.adjoint X‖ ^ 2 ≤ β ^ 2 * ‖X‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hβ 2
  have hn : 0 ≤ ∑ i, 2 * ‖D i + (q i / 2) • X‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith [sq_nonneg ‖Y - B.adjoint X‖]

end InnerProduct

end HeatAnalyticGalerkinEnergy

#print axioms HeatAnalyticGalerkinEnergy.translate_convolution
#print axioms HeatAnalyticGalerkinEnergy.coefficient_mul_polynomial
#print axioms HeatAnalyticGalerkinEnergy.weighted_energy_le_sum_signs
#print axioms HeatAnalyticGalerkinEnergy.translated_drift_lower
