import HeatScalarDampingBound
import HeatTimeTranslation

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatScalarDampingNNReal
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral (f : ℝ≥0 → E) (T : ℝ≥0) :
    (∫ s,f s ∂timeMeasure T)=∫ r in (0:ℝ)..(T:ℝ),f r.toNNReal := by
  have hzero : timeMeasure T=intervalTimeMeasure 0 T := by
    simp only [timeMeasure,intervalTimeMeasure,NNReal.coe_zero]
  rw [hzero,HeatIntervalCovariance.interval_integral]
  change (∫ s in Ioc (0:ℝ) (T:ℝ),f s.toNNReal)=_
  exact (intervalIntegral.integral_of_le T.property).symm

theorem bound {x F : ℝ≥0 → ℝ} {c B : ℝ} {H : ℝ≥0} (hc : 0≤c) (hB : 0≤B)
    (hx : Continuous x) (hF : ∀ t, t≤H → |F t|≤B)
    (heq : ∀ t, t≤H → x t+c*(∫ r,x r ∂timeMeasure t)=F t) :
    ∀ t, t≤H → |x t|≤2*B := by
  have he (r : ℝ) (hr : r∈Icc 0 (H:ℝ)) :
      x r.toNNReal+c*(∫ s in (0:ℝ)..r,x s.toNNReal)=F r.toNNReal := by
    have hrt : r.toNNReal≤H := by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.2
    have hh := heq r.toNNReal hrt
    rw [integral,Real.coe_toNNReal r hr.1] at hh
    exact hh
  have hh := HeatScalarDampingBound.bound hc hB (hx.comp continuous_real_toNNReal)
    (fun r hr => hF r.toNNReal (by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.2)) he
  intro t ht
  simpa only [Function.comp_def,Real.toNNReal_coe] using hh (t:ℝ) ⟨t.property,by exact_mod_cast ht⟩

end HeatScalarDampingNNReal
#check @HeatScalarDampingNNReal.integral
#print axioms HeatScalarDampingNNReal.integral
#check @HeatScalarDampingNNReal.bound
#print HeatScalarDampingNNReal.bound
#print axioms HeatScalarDampingNNReal.bound
