import HeatTorusReal
import SHE.HeatTimeSmoothing
import SHE.ProcessEnergy

set_option autoImplicit false
noncomputable section

namespace HeatTorusHeatSmoothing

open MeasureTheory UnitAddTorus HeatTorusFourier HeatTorusReal
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

private theorem multiplier_increment (P : ℝ) {τ δ θ : ℝ}
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (k : ι → ℤ) :
    ‖multiplier P τ k * (multiplier P δ k - 1)‖ ≤ (δ / τ) ^ θ := by
  let a := frequencySquared P k
  have ha : 0 ≤ a := frequencySquared_nonneg P k
  have hE : Real.exp (-δ * a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) ha)
  rw [norm_mul, multiplier, multiplier, max_eq_left hτ.le, max_eq_left hδ]
  change ‖(Real.exp (-τ * a) : ℂ)‖ * ‖(Real.exp (-δ * a) : ℂ) - 1‖ ≤ _
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonpos (sub_nonpos.mpr hE)]
  rw [neg_sub]
  have h := SHE.HeatTimeSmoothing.scalar_increment_bounds ha hτ hδ
  by_cases hr : δ / τ ≤ 1
  · exact h.1.trans (Real.self_le_rpow_of_le_one (div_nonneg hδ hτ.le) hr hθ₁)
  · exact h.2.trans (Real.one_le_rpow (le_of_not_ge hr) hθ)

theorem bound (P : ℝ) {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (v : State ι) :
    ‖heat P δ (heat P τ v) - heat P τ v‖ ≤ (δ / τ) ^ θ * ‖v‖ := by
  let C := (δ / τ) ^ θ
  let w := heat P δ (heat P τ v) - heat P τ v
  have hcoef (k : ι → ℤ) : mFourierCoeff w k =
      (multiplier P τ k * (multiplier P δ k - 1)) * mFourierCoeff v k := by
    dsimp only [w]
    rw [← coefficientCLM_apply, map_sub, coefficientCLM_apply, coefficientCLM_apply,
      fourierCoeff_heat, fourierCoeff_heat]
    ring
  have hle (k : ι → ℤ) : ‖mFourierCoeff w k‖ ^ 2 ≤ C ^ 2 * ‖mFourierCoeff v k‖ ^ 2 := by
    rw [hcoef, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (multiplier_increment P hτ hδ hθ hθ₁ k) 2) (sq_nonneg _)
  have hs := (hasSum_sq_mFourierCoeff w).summable.tsum_le_tsum hle
    ((hasSum_sq_mFourierCoeff v).summable.mul_left (C ^ 2))
  rw [tsum_mul_left, (hasSum_sq_mFourierCoeff w).tsum_eq, (hasSum_sq_mFourierCoeff v).tsum_eq,
    ← SHE.PredictableL2.realLp_norm_sq, ← SHE.PredictableL2.realLp_norm_sq] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (div_nonneg hδ hτ.le) _) (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hs)

theorem real_bound (P : ℝ) {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (v : RealState ι) :
    ‖realHeat P δ (realHeat P τ v) - realHeat P τ v‖ ≤ (δ / τ) ^ θ * ‖v‖ := by
  change ‖realPart (heat P δ (embed (realHeat P τ v))) - realPart (heat P τ (embed v))‖ ≤ _
  rw [embed_realHeat, ← map_sub]
  have hv := Complex.ofRealCLM.norm_compLp_le v
  rw [Complex.ofRealCLM_norm, one_mul] at hv
  have hw := Complex.reCLM.norm_compLp_le (heat P δ (heat P τ (embed v)) - heat P τ (embed v))
  rw [Complex.reCLM_norm, one_mul] at hw
  exact hw.trans ((bound P hτ hδ hθ hθ₁ (embed v)).trans
    (mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg (div_nonneg hδ hτ.le) _)))

end HeatTorusHeatSmoothing

#print axioms HeatTorusHeatSmoothing.real_bound
