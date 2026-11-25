import HeatScalarDampingNNReal

set_option autoImplicit false
noncomputable section
namespace HeatContinuousTimeIntegral
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuous (x : ℝ≥0 → E) (hx : Continuous x) :
    Continuous (fun t => ∫ s,x s ∂timeMeasure t) := by
  have hxr : Continuous (fun r : ℝ => x r.toNNReal) := hx.comp continuous_real_toNNReal
  have hc := intervalIntegral.continuous_primitive (μ := (volume : Measure ℝ))
    (fun a b => hxr.intervalIntegrable a b) 0
  have he : (fun t => ∫ s,x s ∂timeMeasure t)=
      (fun t : ℝ≥0 => ∫ r in (0:ℝ)..(t:ℝ),x r.toNNReal) := funext (HeatScalarDampingNNReal.integral x)
  rw [he]
  exact hc.comp NNReal.continuous_coe

end HeatContinuousTimeIntegral
#check @HeatContinuousTimeIntegral.continuous
#print HeatContinuousTimeIntegral.continuous
#print axioms HeatContinuousTimeIntegral.continuous
