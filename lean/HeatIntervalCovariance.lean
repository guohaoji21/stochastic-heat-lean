import HeatCovarianceTimeScale
import SHE.IntervalTimeMeasure

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace HeatIntervalCovariance
open MeasureTheory Set SHE.PredictableL2
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def extend (S : ℝ≥0 → E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E := S t.toNNReal

theorem interval_integral (a b : ℝ≥0) (f : ℝ≥0 → E) :
    (∫ s, f s ∂intervalTimeMeasure a b) = ∫ s in Ioc (a:ℝ) (b:ℝ), f s.toNNReal := by
  have hh := nonnegative_coe_measurableEmbedding.integral_map (μ := intervalTimeMeasure a b)
    (fun s : ℝ => f s.toNNReal)
  rw [intervalTimeMeasure_map] at hh
  simpa only [Real.toNNReal_coe] using hh.symm

theorem covariance_interval (S : ℝ≥0 → E →L[ℝ] E) (M : E →L[ℝ] E)
    {H a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H) (y : E) :
    (∫ s in Ioc a b, S (b-s) (M (S (s-a) y)) ∂timeMeasure H) =
      ((b:ℝ)-(a:ℝ)) • ∫ v in (0:ℝ)..1,
        extend S ((1-v)*((b:ℝ)-(a:ℝ))) (M (extend S (v*((b:ℝ)-(a:ℝ))) y)) := by
  rw [timeMeasure_restrict_Ioc a hbH,interval_integral]
  have he : (∫ s in Ioc (a:ℝ) (b:ℝ), S (b-s.toNNReal) (M (S (s.toNNReal-a) y))) =
      ∫ s in (a:ℝ)..(b:ℝ), extend S ((b:ℝ)-s) (M (extend S (s-(a:ℝ)) y)) := by
    rw [intervalIntegral.integral_of_le (show (a:ℝ) ≤ (b:ℝ) by exact_mod_cast hab)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 ≤ s := a.property.trans hs.1.le
    have hsb : s.toNNReal ≤ b := by exact_mod_cast (Real.coe_toNNReal s hs0 ▸ hs.2)
    have hsa : a ≤ s.toNNReal := by exact_mod_cast (Real.coe_toNNReal s hs0 ▸ hs.1.le)
    unfold extend
    have h1 := congrArg Real.toNNReal (NNReal.coe_sub hsb)
    have h2 := congrArg Real.toNNReal (NNReal.coe_sub hsa)
    simp only [Real.toNNReal_coe, Real.coe_toNNReal s hs0] at h1 h2
    rw [h1,h2]
  rw [he]
  let r : ℝ := (b:ℝ)-(a:ℝ)
  let f : ℝ → E := fun v => extend S (r-v) (M (extend S v y))
  have hfun : (fun s : ℝ => extend S ((b:ℝ)-s) (M (extend S (s-(a:ℝ)) y))) =
      (fun s => f (s-(a:ℝ))) := by
    funext s
    dsimp only [f]
    rw [show (b:ℝ)-s = r-(s-(a:ℝ)) by dsimp [r]; ring]
  rw [hfun]
  have ht := intervalIntegral.integral_comp_sub_right (a := (a:ℝ)) (b := (b:ℝ)) f (a:ℝ)
  rw [sub_self] at ht
  rw [ht]
  exact HeatCovarianceTimeScale.covariance_time_change (extend S) M r y

end HeatIntervalCovariance
#check @HeatIntervalCovariance.interval_integral
#print axioms HeatIntervalCovariance.interval_integral
#check @HeatIntervalCovariance.covariance_interval
#print axioms HeatIntervalCovariance.covariance_interval
