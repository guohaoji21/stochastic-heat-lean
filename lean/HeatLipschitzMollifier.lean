import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
noncomputable section

namespace HeatLipschitzMollifier

open ContinuousLinearMap MeasureTheory Metric Filter Set
open scoped Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Convolution with a nonnegative bump of unit mass preserves the
Lipschitz constant and every translation period while smoothing uniformly. -/
theorem exists_smooth_periodic_approx (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : LipschitzWith 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ LipschitzWith 1 g ∧
      (∀ x, |g x - f x| ≤ ε) ∧
      (∀ p : E, (∀ x, f (x + p) = f x) → ∀ x, g (x + p) = g x) := by
  let B : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let k := B.normed μ
  let g := (k ⋆[lsmul ℝ ℝ, μ] f)
  have hc : Continuous f := hf.continuous
  have hg (x : E) : g x = ∫ y, k y * f (x - y) ∂μ := rfl
  have hi (x : E) : Integrable (fun y => k y * f (x - y)) μ := by
    have hk : Continuous k := B.continuous_normed
    have hprod : Continuous (fun y => k y * f (x - y)) :=
      hk.mul (hc.comp (continuous_const.sub continuous_id))
    apply hprod.integrable_of_hasCompactSupport
    exact (B.hasCompactSupport_normed (μ := μ)).of_isClosed_subset
      (isClosed_tsupport _) tsupport_mul_subset_left
  refine ⟨g, B.hasCompactSupport_normed.contDiff_convolution_left _ B.contDiff_normed
    hc.locallyIntegrable, ?_, ?_, ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x z
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, hg]
    rw [← integral_sub (hi x) (hi z), ← Real.norm_eq_abs]
    calc
      _ ≤ ∫ y, k y * dist x z ∂μ := by
        apply norm_integral_le_of_norm_le (B.integrable_normed.mul_const _) (Eventually.of_forall _)
        intro y
        rw [← mul_sub, norm_mul, Real.norm_of_nonneg (B.nonneg_normed y), ← dist_eq_norm]
        apply mul_le_mul_of_nonneg_left _ (B.nonneg_normed y)
        simpa only [NNReal.coe_one, one_mul, dist_sub_right] using hf.dist_le_mul (x - y) (z - y)
      _ = _ := by rw [integral_mul_const, B.integral_normed, one_mul]
  · intro x
    rw [← Real.dist_eq]
    apply B.dist_normed_convolution_le hc.aestronglyMeasurable
    intro y hy
    have h : dist y x ≤ ε := (show dist y x < ε from hy).le
    exact (by simpa only [NNReal.coe_one, one_mul] using hf.dist_le_mul y x :
      dist (f y) (f x) ≤ dist y x).trans h
  · intro p hp x
    rw [hg, hg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change k y * f (x + p - y) = k y * f (x - y)
      rw [show x + p - y = (x - y) + p by abel, hp]

/-- The bound on the Fréchet derivative of a Euclidean one-Lipschitz
function gives the exact bound on the sum of its squared partial derivatives. -/
theorem gradient_sq_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f) (x : EuclideanSpace ℝ ι) :
    ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 ≤ 1 := by
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm (fderiv ℝ f x)
  have hv : ‖v‖ ≤ 1 := by
    rw [show ‖v‖ = ‖fderiv ℝ f x‖ from
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map (fderiv ℝ f x)]
    exact norm_fderiv_le_of_lipschitz ℝ hf
  have he (i : ι) : fderiv ℝ f x (EuclideanSpace.single i 1) = v i := by
    rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right]
    simp [v]
  simp_rw [he]
  have hs : ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) v
  rw [← hs]
  nlinarith [norm_nonneg v]

end HeatLipschitzMollifier

#print axioms HeatLipschitzMollifier.exists_smooth_periodic_approx
#print axioms HeatLipschitzMollifier.gradient_sq_le_one
