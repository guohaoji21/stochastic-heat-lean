import HeatTorusSubeigen
import HeatEulerScalar
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace HeatTorusResolvent

open MeasureTheory Filter Set UnitAddTorus HeatTorusFourier HeatTorusReal
open scoped NNReal ENNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

private def clock : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun s => ENNReal.ofReal (Real.exp (-s)))

private instance : IsProbabilityMeasure clock where
  measure_univ := by
    rw [clock, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
        (Eventually.of_forall fun s => (Real.exp_pos (-s)).le),
      integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

private theorem integral_clock {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → E) :
    (∫ s, F s ∂clock) = ∫ s in Ioi (0 : ℝ), Real.exp (-s) • F s := by
  change (∫ s, F s ∂(volume.restrict (Ioi 0)).withDensity
    (fun s => ((Real.toNNReal (Real.exp (-s)) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]

private theorem orbit_integrable (P : ℝ) (a : ℝ≥0) (f : RealState ι) :
    Integrable (fun s : ℝ => realHeat P ((a : ℝ) * s) f) clock := by
  apply (integrable_const ‖f‖).mono'
  · exact ((continuous_realHeat P f).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun s => realHeat_contraction P _ f

/-- The real torus resolvent step, obtained by averaging the actual heat orbit
against the unit exponential distribution. -/
def step (P : ℝ) (a : ℝ≥0) : RealState ι →L[ℝ] RealState ι :=
  (show RealState ι →ₗ[ℝ] RealState ι from
    { toFun := fun f => ∫ s, realHeat P ((a : ℝ) * s) f ∂clock
      map_add' := fun f g => by
        simp only [map_add, integral_add (orbit_integrable P a f) (orbit_integrable P a g)]
      map_smul' := fun c f => by simp only [map_smul, integral_smul, RingHom.id_apply] }).mkContinuous 1
    fun f => by
      rw [one_mul]
      refine (norm_integral_le_integral_norm _).trans ?_
      simpa only [integral_const, probReal_univ, one_smul] using
        (integral_mono (orbit_integrable P a f).norm (integrable_const ‖f‖)
          (fun s => realHeat_contraction P ((a : ℝ) * s) f))

theorem step_nonnegative (P : ℝ) (a : ℝ≥0) (f : RealState ι)
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x) : ∀ᵐ x ∂volume, 0 ≤ step P a f x :=
  HeatTorusGaussian.integral_nonnegative clock _ (orbit_integrable P a f)
    (Eventually.of_forall fun s => HeatTorusGaussian.realHeat_nonnegative P ((a : ℝ) * s) f hf)

private def coord (k : ι → ℤ) : RealState ι →L[ℝ] ℂ :=
  (coefficientCLM k).comp embed

private theorem coord_apply (k : ι → ℤ) (f : RealState ι) :
    coord k f = mFourierCoeff (embed f) k :=
  coefficientCLM_apply k (embed f)

theorem coefficient_step (P : ℝ) (a : ℝ≥0) (f : RealState ι) (k : ι → ℤ) :
    mFourierCoeff (embed (step P a f)) k =
      (↑((1 + (a : ℝ) * frequencySquared P k)⁻¹) : ℂ) * mFourierCoeff (embed f) k := by
  rw [← coord_apply]
  change coord k (∫ s, realHeat P ((a : ℝ) * s) f ∂clock) = _
  rw [← (coord k).integral_comp_comm (orbit_integrable P a f), integral_clock]
  let c := 1 + (a : ℝ) * frequencySquared P k
  let z := mFourierCoeff (embed f) k
  have hc : 0 < c := add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg a.property (frequencySquared_nonneg P k))
  have h : (∫ s in Ioi (0 : ℝ), Real.exp (-s) • coord k (realHeat P ((a : ℝ) * s) f)) =
      ∫ s in Ioi (0 : ℝ), (Real.exp (-c * s) : ℂ) * z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [coord_apply, embed_realHeat, fourierCoeff_heat, Complex.real_smul, multiplier,
      ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have he : -s + -max ((a : ℝ) * s) 0 * frequencySquared P k = -c * s := by
      have has : (0 : ℝ) ≤ (a : ℝ) * s := mul_nonneg a.property (show (0 : ℝ) < s from hs).le
      rw [show max ((a : ℝ) * s) (0 : ℝ) = (a : ℝ) * s from max_eq_left has]
      dsimp [c]
      ring
    rw [he]
  have hi : (∫ s in Ioi (0 : ℝ), Real.exp (-c * s)) = c⁻¹ := by
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hc), mul_zero, Real.exp_zero, div_neg, neg_div,
      neg_neg, one_div]
  rw [h, integral_mul_const, integral_complex_ofReal, hi]

/-- The exponential average solves the right-generator resolvent equation. -/
theorem generator_step (P : ℝ) (a : ℝ≥0) (ha : 0 < a) (f : RealState ι) :
    HasDerivWithinAt (fun t : ℝ => realHeat P t (step P a f))
      ((a : ℝ)⁻¹ • (step P a f - f)) (Ici 0) 0 := by
  apply (HeatTorusSubeigen.generator_iff_coefficients P _ _).mpr
  intro k
  rw [← coord_apply k ((a : ℝ)⁻¹ • (step P a f - f)), map_smul, map_sub,
    coord_apply k (step P a f), coefficient_step, coord_apply k f,
    Complex.real_smul]
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
  have hc : (1 + (a : ℝ) * frequencySquared P k : ℝ) ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg a.property (frequencySquared_nonneg P k)))
  have hcC : (1 + ((a : ℝ) : ℂ) * (frequencySquared P k : ℂ)) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ha', hcC]
  <;> ring

end HeatTorusResolvent

#print axioms HeatTorusResolvent.step_nonnegative
#print axioms HeatTorusResolvent.coefficient_step
#print axioms HeatTorusResolvent.generator_step
