import HeatTorusSubeigen
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace HeatTorusFourierDerivatives

open Complex MeasureTheory

/-- Integration by parts on a unit period, including the zero mode. -/
theorem coefficient_derivative (f f' : UnitAddCircle → ℂ) (hf' : Continuous f')
    (hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : UnitAddCircle)) (f' (x : UnitAddCircle)) x)
    (n : ℤ) : fourierCoeff f' n = (2 * Real.pi * I * n) * fourierCoeff f n := by
  let χ := fun x : ℝ => fourier (-n) (x : UnitAddCircle)
  let c : ℂ := 2 * Real.pi * I * n
  have he (x : ℝ) : HasDerivAt χ (-c * χ x) x := by
    simpa only [χ, c, div_one, ofReal_one, neg_mul] using hasDerivAt_fourier_neg 1 n x
  have hD (x : ℝ) : HasDerivAt (fun y : ℝ => χ y * f (y : UnitAddCircle))
      (χ x * f' (x : UnitAddCircle) - c * (χ x * f (x : UnitAddCircle))) x := by
    convert (he x).mul (hd x) using 1
    ring
  have hχ : Continuous χ := continuous_iff_continuousAt.mpr fun x => (he x).continuousAt
  have hreal : Continuous (fun x : ℝ => f (x : UnitAddCircle)) :=
    continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hreal' : Continuous (fun x : ℝ => f' (x : UnitAddCircle)) :=
    hf'.comp (AddCircle.continuous_mk' 1)
  have h₁ : IntervalIntegrable (fun x : ℝ => χ x * f' (x : UnitAddCircle)) volume 0 1 :=
    (hχ.mul hreal').intervalIntegrable 0 1
  have h₂ : IntervalIntegrable (fun x : ℝ => c * (χ x * f (x : UnitAddCircle))) volume 0 1 :=
    (continuous_const.mul (hχ.mul hreal)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x) (h₁.sub h₂)
  have hperiod : ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := AddCircle.coe_period 1
  change (∫ x in (0 : ℝ)..1, χ x * f' (x : UnitAddCircle) - c * (χ x * f (x : UnitAddCircle))) =
    χ 1 * f ((1 : ℝ) : UnitAddCircle) - χ 0 * f ((0 : ℝ) : UnitAddCircle) at h
  rw [intervalIntegral.integral_sub h₁ h₂, intervalIntegral.integral_const_mul] at h
  have hχperiod : χ 1 = χ 0 := congrArg (fun x : UnitAddCircle => fourier (-n) x) hperiod
  rw [hχperiod, hperiod, sub_self, sub_eq_zero] at h
  simpa only [fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ), one_div_one, one_smul,
    zero_add, smul_eq_mul, χ, c] using h

theorem coefficient_second_derivative (f f' f'' : UnitAddCircle → ℂ)
    (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : UnitAddCircle)) (f' (x : UnitAddCircle)) x)
    (hdd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f' (y : UnitAddCircle)) (f'' (x : UnitAddCircle)) x)
    (n : ℤ) : fourierCoeff f'' n = (↑(-((2 * Real.pi : ℝ) ^ 2 * (n : ℝ) ^ 2)) : ℂ) *
      fourierCoeff f n := by
  rw [coefficient_derivative f' f'' hf'' hdd, coefficient_derivative f f' hf' hd]
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * n)^2 * fourierCoeff f n * Complex.I_sq

end HeatTorusFourierDerivatives

#print axioms HeatTorusFourierDerivatives.coefficient_derivative
#print axioms HeatTorusFourierDerivatives.coefficient_second_derivative
