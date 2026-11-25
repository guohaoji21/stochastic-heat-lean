import SHE.PredictableTime
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatZeroGronwall
open MeasureTheory Set SHE.PredictableL2
open scoped NNReal

theorem zero (H : ℝ≥0) (f : ℝ≥0 → ℝ) (hf : Continuous f) (hf0 : ∀ t,0 ≤ f t)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t,t ≤ H → f t ≤ C*(∫ s,f s ∂timeMeasure t)) :
    ∀ t,t ≤ H → f t=0 := by
  let fR := fun x : ℝ => f x.toNNReal
  let P := fun x : ℝ => ∫ s in (0:ℝ)..x,fR s
  have hc : Continuous fR := hf.comp continuous_real_toNNReal
  have hd (x : ℝ) : HasDerivAt P (fR x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hi (t : ℝ≥0) : (∫ s,f s ∂timeMeasure t)=P (t:ℝ) := by
    rw [timeMeasure_integral]
    exact (intervalIntegral.integral_of_le (f := fR) (μ := volume) t.property).symm
  intro t ht
  have hP := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := P) (f' := fR) (K := C) (a := 0) (b := (t:ℝ))
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt) (by simp [P]) (by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hxt : x.toNNReal ≤ t := by
        exact_mod_cast (Real.coe_toNNReal x hx0 ▸ hx.2.le)
      have hb := hbound x.toNNReal (hxt.trans ht)
      rw [hi,Real.coe_toNNReal x hx0] at hb
      rw [Real.norm_eq_abs,abs_of_nonneg (hf0 _)]
      exact hb.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)) (t:ℝ) ⟨t.property,le_rfl⟩
  have hb := hbound t ht
  rw [hi,hP,mul_zero] at hb
  exact le_antisymm hb (hf0 t)

end HeatZeroGronwall
#check @HeatZeroGronwall.zero
#print axioms HeatZeroGronwall.zero
