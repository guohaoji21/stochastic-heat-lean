import HeatTorusResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace HeatTorusEuler

open MeasureTheory Filter UnitAddTorus HeatTorusFourier HeatTorusReal
open scoped NNReal ENNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

theorem coefficient_iterate (P : ℝ) (a : ℝ≥0) (f : RealState ι) (n : ℕ) (k : ι → ℤ) :
    mFourierCoeff (embed (((HeatTorusResolvent.step P a : RealState ι → RealState ι)^[n]) f)) k =
      (↑(((1 + (a : ℝ) * frequencySquared P k)⁻¹) ^ n) : ℂ) * mFourierCoeff (embed f) k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', HeatTorusResolvent.coefficient_step, ih,
      pow_succ', Complex.ofReal_mul, mul_assoc]

/-- Backward Euler applied to the real torus resolvent converges in spatial
`L²` to the Fourier heat flow on every initial state. -/
theorem tendsto_heat (P : ℝ) (T : ℝ≥0) (f : RealState ι) :
    Tendsto (fun n : ℕ => (((HeatTorusResolvent.step P (T / (n : ℝ≥0)) :
      RealState ι → RealState ι)^[n]) f)) atTop (𝓝 (realHeat P T f)) := by
  let u (n : ℕ) := ((HeatTorusResolvent.step P (T / (n : ℝ≥0)) :
    RealState ι → RealState ι)^[n]) f
  let v := realHeat P T f
  let z := embed (ι := ι) f
  let U (n : ℕ) := embed (u n)
  let V := embed v
  have hu (n : ℕ) (k : ι → ℤ) : mFourierCoeff (U n) k =
      (↑(((1 + (T : ℝ) * frequencySquared P k / (n : ℝ))⁻¹) ^ n) : ℂ) *
        mFourierCoeff z k := by
    change mFourierCoeff (embed (u n)) k = _
    dsimp only [u]
    rw [coefficient_iterate]
    simp only [NNReal.coe_div, NNReal.coe_natCast, div_mul_eq_mul_div, z]
  have hV (k : ι → ℤ) : mFourierCoeff V k =
      (Real.exp (-(T : ℝ) * frequencySquared P k) : ℂ) * mFourierCoeff z k := by
    change mFourierCoeff (embed (realHeat P T f)) k = _
    rw [embed_realHeat, fourierCoeff_heat, multiplier,
      show max (T : ℝ) (0 : ℝ) = (T : ℝ) from max_eq_left T.property]
  have hlim (k : ι → ℤ) :
      Tendsto (fun n => mFourierCoeff (U n) k) atTop (𝓝 (mFourierCoeff V k)) := by
    simp_rw [hu, hV]
    simpa only [Function.comp_def, neg_mul] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (HeatEulerScalar.tendsto_inverse ((T : ℝ) * frequencySquared P k))).mul_const
          (mFourierCoeff z k)
  have hub (n : ℕ) (k : ι → ℤ) : ‖mFourierCoeff (U n) k‖ ≤ ‖mFourierCoeff z k‖ := by
    rw [hu, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnonneg : (0 : ℝ) ≤ (T : ℝ) * frequencySquared P k / (n : ℝ) :=
      div_nonneg (mul_nonneg T.property (frequencySquared_nonneg P k)) (Nat.cast_nonneg n)
    have hle : (1 + (T : ℝ) * frequencySquared P k / (n : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith)
    have hpos : 0 ≤ (1 + (T : ℝ) * frequencySquared P k / (n : ℝ))⁻¹ := by positivity
    rw [abs_of_nonneg (pow_nonneg hpos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hpos hle)
  have hvb (k : ι → ℤ) : ‖mFourierCoeff V k‖ ≤ ‖mFourierCoeff z k‖ := by
    change ‖mFourierCoeff (embed (realHeat P T f)) k‖ ≤ _
    rw [embed_realHeat, fourierCoeff_heat, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (multiplier_norm_le P T k)
  have hdiff (n : ℕ) (k : ι → ℤ) :
      mFourierCoeff (U n - V) k = mFourierCoeff (U n) k - mFourierCoeff V k := by
    simp only [← coefficientCLM_apply, map_sub]
  have hd (k : ι → ℤ) :
      Tendsto (fun n => ‖mFourierCoeff (U n - V) k‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hdiff, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((hlim k).sub_const (mFourierCoeff V k)).norm.pow 2
  have he (n : ℕ) (k : ι → ℤ) :
      ‖‖mFourierCoeff (U n - V) k‖ ^ 2‖ ≤ 4 * ‖mFourierCoeff z k‖ ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _), hdiff]
    have hle := (norm_sub_le (mFourierCoeff (U n) k) (mFourierCoeff V k)).trans
      (add_le_add (hub n k) (hvb k))
    exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans_eq (by ring)
  have hp (g : State ι) : ‖g‖ ^ 2 = ∑' k : ι → ℤ, ‖mFourierCoeff g k‖ ^ 2 := by
    rw [← (mFourierBasis (d := ι)).repr.norm_map g]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mFourierBasis_repr] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (mFourierBasis.repr g))
  have hs := tendsto_tsum_of_dominated_convergence
    ((hasSum_sq_mFourierCoeff z).summable.mul_left 4) hd (Eventually.of_forall he)
  have hsq : Tendsto (fun n => ‖U n - V‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [← hp, tsum_zero] using hs
  have hc : Tendsto U atTop (𝓝 V) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [u, v, U, V, Function.comp_def, realPart_embed] using
    (realPart (ι := ι)).continuous.continuousAt.tendsto.comp hc

end HeatTorusEuler

#print axioms HeatTorusEuler.tendsto_heat
