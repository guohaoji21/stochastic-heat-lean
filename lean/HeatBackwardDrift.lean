import HeatBackwardCell
import HeatCovarianceOperator

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatBackwardDrift
open MeasureTheory Set HeatIntervalCovariance HeatCovarianceOperator
open SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

theorem reverse_time_change (r : ℝ) (q : E) :
    (∫ u in (0:ℝ)..r, HeatIntervalCovariance.extend S u (M (HeatIntervalCovariance.extend S (r-u) q))) =
      r • ∫ v in (0:ℝ)..1, HeatIntervalCovariance.extend S (v*r)
        (M (HeatIntervalCovariance.extend S ((1-v)*r) q)) := by
  let f : ℝ → E := fun u => HeatIntervalCovariance.extend S u (M (HeatIntervalCovariance.extend S (r-u) q))
  have ht := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) f r
  simp only [mul_zero,mul_one] at ht
  have he : (fun v : ℝ => f (r*v)) = (fun v => HeatIntervalCovariance.extend S (v*r)
      (M (HeatIntervalCovariance.extend S ((1-v)*r) q))) := by
    funext v
    dsimp [f]
    rw [mul_comm r v,show r-v*r = (1-v)*r by ring]
  rw [he] at ht
  exact ht.symm

include hS hcontr in
theorem reverse_mean (r : ℝ≥0) (q : E) :
    (∫ v in (0:ℝ)..1, HeatIntervalCovariance.extend S (v*(r:ℝ))
      (M (HeatIntervalCovariance.extend S ((1-v)*(r:ℝ)) q))) = covariance S hS hcontr M r q := by
  have hf : (fun v : ℝ => HeatIntervalCovariance.extend S (v*(r:ℝ))
      (M (HeatIntervalCovariance.extend S ((1-v)*(r:ℝ)) q))) =
      (fun v => integrand S M r q (1-v)) := by
    funext v
    unfold integrand
    rw [show 1-(1-v) = v by ring]
  rw [hf,intervalIntegral.integral_comp_sub_left]
  norm_num only [sub_self,sub_zero]
  exact (covariance_apply S hS hcontr M r q).symm

theorem real_formula {H a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H) (q : E) :
    HeatBackwardCell.drift H S M a b q =
      ∫ u in (0:ℝ)..((b:ℝ)-(a:ℝ)), HeatIntervalCovariance.extend S u
        (M (HeatIntervalCovariance.extend S (((b:ℝ)-(a:ℝ))-u) q)) := by
  unfold HeatBackwardCell.drift
  rw [timeMeasure_restrict_Ioc a hbH,interval_integral]
  have he : (∫ s in Ioc (a:ℝ) (b:ℝ), S (s.toNNReal-a) (M (S (b-s.toNNReal) q))) =
      ∫ s in (a:ℝ)..(b:ℝ), HeatIntervalCovariance.extend S (s-(a:ℝ))
        (M (HeatIntervalCovariance.extend S ((b:ℝ)-s) q)) := by
    rw [intervalIntegral.integral_of_le (show (a:ℝ) ≤ (b:ℝ) by exact_mod_cast hab)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 ≤ s := a.property.trans hs.1.le
    have hsb : s.toNNReal ≤ b := by exact_mod_cast (Real.coe_toNNReal s hs0 ▸ hs.2)
    have hsa : a ≤ s.toNNReal := by exact_mod_cast (Real.coe_toNNReal s hs0 ▸ hs.1.le)
    have h1 := congrArg Real.toNNReal (NNReal.coe_sub hsb)
    have h2 := congrArg Real.toNNReal (NNReal.coe_sub hsa)
    simp only [Real.toNNReal_coe,Real.coe_toNNReal s hs0] at h1 h2
    unfold HeatIntervalCovariance.extend
    rw [h1,h2]
  rw [he]
  let f : ℝ → E := fun u => HeatIntervalCovariance.extend S u
    (M (HeatIntervalCovariance.extend S (((b:ℝ)-(a:ℝ))-u) q))
  have hf : (fun s : ℝ => HeatIntervalCovariance.extend S (s-(a:ℝ))
      (M (HeatIntervalCovariance.extend S ((b:ℝ)-s) q))) = (fun s => f (s-(a:ℝ))) := by
    funext s
    dsimp only [f]
    rw [show (b:ℝ)-s = ((b:ℝ)-(a:ℝ))-(s-(a:ℝ)) by ring]
  rw [hf,intervalIntegral.integral_comp_sub_right]
  simp only [sub_self]
  rfl

include hS hcontr in
theorem drift_covariance {H a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H) (q : E) :
    HeatBackwardCell.drift H S M a b q = ((b-a:ℝ≥0):ℝ) • covariance S hS hcontr M (b-a) q := by
  rw [real_formula S M hab hbH,reverse_time_change,← NNReal.coe_sub hab,reverse_mean S hS hcontr M]

include hS hcontr in
theorem drift_all_times {H b : ℝ≥0} (hbH : b ≤ H) (q : E) (a : ℝ≥0) :
    HeatBackwardCell.drift H S M a b q = ((b-a:ℝ≥0):ℝ) • covariance S hS hcontr M (b-a) q := by
  by_cases hab : a ≤ b
  · exact drift_covariance S hS hcontr M hab hbH q
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    simp only [HeatBackwardCell.drift,Ioc_eq_empty_of_le hba,Measure.restrict_empty,integral_zero_measure,
      tsub_eq_zero_of_le hba,NNReal.coe_zero,zero_smul]

include hS hcontr in
theorem drift_continuous {H b : ℝ≥0} (hbH : b ≤ H) (q : E) :
    Continuous (fun a => HeatBackwardCell.drift H S M a b q) := by
  have hrem := HeatPredictableSemigroup.continuous_remaining b
  have hc : Continuous (fun a : ℝ≥0 => ((b-a:ℝ≥0):ℝ) • covariance S hS hcontr M (b-a) q) :=
    (continuous_subtype_val.comp hrem).smul
      ((covariance_continuous S hS hcontr M q).comp hrem)
  exact hc.congr (fun a => (drift_all_times S hS hcontr M hbH q a).symm)

include hS hcontr in
theorem state_continuous {Ω : Type*} {H b : ℝ≥0} (hbH : b ≤ H)
    (W : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => W t ω)) (a : ℝ≥0) (q : E) (ω : Ω) :
    Continuous (fun t => HeatBackwardCell.state H S M W a b q t ω) :=
  ((hc ω).sub continuous_const).smul ((hS q).comp (HeatPredictableSemigroup.continuous_remaining b)) |>.add
    (drift_continuous S hS hcontr M hbH q)

end HeatBackwardDrift
#check @HeatBackwardDrift.reverse_time_change
#print axioms HeatBackwardDrift.reverse_time_change
#check @HeatBackwardDrift.reverse_mean
#print axioms HeatBackwardDrift.reverse_mean
#check @HeatBackwardDrift.real_formula
#print axioms HeatBackwardDrift.real_formula
#check @HeatBackwardDrift.drift_covariance
#print axioms HeatBackwardDrift.drift_covariance
#check @HeatBackwardDrift.drift_all_times
#print axioms HeatBackwardDrift.drift_all_times
#check @HeatBackwardDrift.drift_continuous
#print axioms HeatBackwardDrift.drift_continuous
#check @HeatBackwardDrift.state_continuous
#print axioms HeatBackwardDrift.state_continuous
