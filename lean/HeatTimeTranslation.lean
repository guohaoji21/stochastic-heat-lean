import HeatIntervalCovariance

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatTimeTranslation
open MeasureTheory Set SHE.PredictableL2
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_shift (f : ℝ≥0 → E) {H s T : ℝ≥0} (hsT : s≤T) (hTH : T≤H) :
    (∫ r in Ioc s T,f (r-s) ∂timeMeasure H)=∫ r,f r ∂timeMeasure (T-s) := by
  rw [timeMeasure_restrict_Ioc s hTH,HeatIntervalCovariance.interval_integral]
  have hzero : timeMeasure (T-s)=intervalTimeMeasure 0 (T-s) := by
    simp only [timeMeasure,intervalTimeMeasure,NNReal.coe_zero]
  rw [hzero,HeatIntervalCovariance.interval_integral]
  have he : (∫ r in Ioc (s:ℝ) (T:ℝ),f (r.toNNReal-s))=
      ∫ r in (s:ℝ)..(T:ℝ),f (r-(s:ℝ)).toNNReal := by
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hsT)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hsr : s≤r.toNNReal := by exact_mod_cast (Real.coe_toNNReal r (s.property.trans_lt hr.1).le ▸ hr.1.le)
    have hh := congrArg Real.toNNReal (NNReal.coe_sub hsr)
    simp only [Real.toNNReal_coe,Real.coe_toNNReal r (s.property.trans_lt hr.1).le] at hh
    exact congrArg f hh
  have ht := intervalIntegral.integral_comp_sub_right (a := (s:ℝ)) (b := (T:ℝ))
    (fun r : ℝ => f r.toNNReal) (s:ℝ)
  rw [he,ht]
  simp only [sub_self]
  rw [intervalIntegral.integral_of_le (sub_nonneg.mpr (by exact_mod_cast hsT)),NNReal.coe_sub hsT]
  rfl

end HeatTimeTranslation
#check @HeatTimeTranslation.integral_shift
#print HeatTimeTranslation.integral_shift
#print axioms HeatTimeTranslation.integral_shift
