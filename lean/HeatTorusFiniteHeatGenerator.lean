import HeatTorusProjectedConvolution
import HeatAffineEnergyClock
import HeatTimeTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace HeatTorusFiniteHeatGenerator

open Filter MeasureTheory Set SHE.PredictableL2
open HeatTorusGalerkinBackward (State laplace)
open HeatTorusProjectedConvolution (finiteHeat)
open scoped NNReal

variable {ι : Type*} [Fintype ι]

private theorem exponential_primitive (freq : ℝ) (t : ℝ≥0) :
    (∫ s, (-freq) * Real.exp ((-freq) * (s : ℝ)) ∂timeMeasure t) =
      Real.exp ((-freq) * (t : ℝ)) - 1 := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.property
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => Real.exp ((-freq) * r)) ((-freq) * Real.exp ((-freq) * s)) s := by
    have hlin : HasDerivAt (fun r : ℝ => (-freq) * r) (-freq) s := by
      simpa only [mul_one] using (hasDerivAt_id' s).const_mul (-freq)
    simpa only [mul_comm (Real.exp _)] using hlin.exp
  have hi : IntervalIntegrable (fun r : ℝ => (-freq) * Real.exp ((-freq) * r)) volume 0 (t : ℝ) :=
    (show Continuous (fun r : ℝ => (-freq) * Real.exp ((-freq) * r)) by fun_prop).intervalIntegrable _ _
  rw [HeatAffineEnergyClock.integral]
  calc
    _ = ∫ r in (0 : ℝ)..(t : ℝ), (-freq) * Real.exp ((-freq) * r) := by
      simp only [intervalIntegral.integral_of_le ht]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.coe_toNNReal _ hr.1.le]
    _ = _ := by
      simpa only [mul_zero, Real.exp_zero] using
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi

/-- The finite heat family has the actual Galerkin Laplacian as generator,
in the integrated form used by the forward equation. -/
theorem integrated (S : Finset (ι → ℤ)) (P : ℝ) (t : ℝ≥0) (x : State S) :
    (∫ s, laplace S P (finiteHeat S P s x) ∂timeMeasure t) = finiteHeat S P t x - x := by
  have hi : Integrable (fun s => laplace S P (finiteHeat S P s x)) (timeMeasure t) := by
    apply (integrable_const (‖laplace S P‖ * ‖x‖)).mono'
    · exact ((laplace S P).continuous.comp (HeatTorusProjectedConvolution.finiteHeat_continuous S P x)).aestronglyMeasurable
    · exact Eventually.of_forall fun s => ((laplace S P).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (HeatTorusProjectedConvolution.finiteHeat_contraction S P s x) (norm_nonneg _))
  ext k
  let L := (EuclideanSpace.proj (𝕜 := ℂ) k).restrictScalars ℝ
  let freq := HeatTorusFourier.frequencySquared P k.val
  let R := (ContinuousLinearMap.id ℝ ℝ).smulRight (x k)
  change L (∫ s, laplace S P (finiteHeat S P s x) ∂timeMeasure t) = (finiteHeat S P t x - x) k
  rw [← L.integral_comp_comm hi]
  have hpoint (s : ℝ≥0) : L (laplace S P (finiteHeat S P s x)) = R ((-freq) * Real.exp ((-freq) * (s : ℝ))) := by
    change laplace S P (finiteHeat S P s x) k = (((-freq) * Real.exp ((-freq) * (s : ℝ)) : ℝ) : ℂ) * x k
    have hmul : -(s : ℝ) * HeatTorusFourier.frequencySquared P k.val = (-freq) * (s : ℝ) := by
      dsimp [freq]
      ring
    rw [HeatTorusGalerkinBackward.laplace_apply, HeatTorusProjectedConvolution.finiteHeat_apply,
      HeatTorusFourier.multiplier, max_eq_left (show (0 : ℝ) ≤ (s : ℝ) by positivity),
      hmul, Complex.ofReal_mul, mul_assoc]
  simp_rw [hpoint]
  have hreal : Integrable (fun s : ℝ≥0 => (-freq) * Real.exp ((-freq) * (s : ℝ))) (timeMeasure t) := by
    apply (integrable_const |freq|).mono'
    · exact (show Continuous (fun s : ℝ≥0 => (-freq) * Real.exp ((-freq) * (s : ℝ))) by fun_prop).aestronglyMeasurable
    · apply Eventually.of_forall
      intro s
      rw [norm_mul, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      apply mul_le_of_le_one_right (abs_nonneg _)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (HeatTorusFourier.frequencySquared_nonneg P _)) s.property)
  rw [R.integral_comp_comm hreal, exponential_primitive]
  change (((Real.exp ((-freq) * (t : ℝ)) - 1 : ℝ) : ℂ) * x k) = finiteHeat S P t x k - x k
  have hmul : -(t : ℝ) * HeatTorusFourier.frequencySquared P k.val = (-freq) * (t : ℝ) := by
    dsimp [freq]
    ring
  rw [HeatTorusProjectedConvolution.finiteHeat_apply, HeatTorusFourier.multiplier,
    max_eq_left (show (0 : ℝ) ≤ (t : ℝ) by positivity), hmul,
    Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]

theorem integrated_shift (S : Finset (ι → ℤ)) (P : ℝ) {a t : ℝ≥0} (hat : a ≤ t) (x : State S) :
    (∫ s in Ioc a t, laplace S P (finiteHeat S P (s - a) x) ∂timeMeasure t) =
      finiteHeat S P (t - a) x - x := by
  rw [HeatTimeTranslation.integral_shift (fun s => laplace S P (finiteHeat S P s x)) hat le_rfl, integrated]

end HeatTorusFiniteHeatGenerator

#print axioms HeatTorusFiniteHeatGenerator.integrated
#print axioms HeatTorusFiniteHeatGenerator.integrated_shift
