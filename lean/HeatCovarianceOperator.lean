import HeatIntervalCovariance
import HeatPredictableStateInput
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatCovarianceOperator
open MeasureTheory Set HeatIntervalCovariance
open scoped NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

def integrand (r : ℝ≥0) (y : E) (v : ℝ) : E :=
  extend S ((1-v)*(r:ℝ)) (M (extend S (v*(r:ℝ)) y))

include hS hcontr in
theorem joint_continuous (y : E) : Continuous (fun p : ℝ≥0 × ℝ => integrand S M p.1 y p.2) := by
  have ha := HeatPredictableSemigroup.continuous_action S hS hcontr
  have ht1 : Continuous (fun p : ℝ≥0 × ℝ => Real.toNNReal ((1-p.2)*(p.1:ℝ))) := by fun_prop
  have ht2 : Continuous (fun p : ℝ≥0 × ℝ => Real.toNNReal (p.2*(p.1:ℝ))) := by fun_prop
  have hY : Continuous (fun p : ℝ≥0 × ℝ => S (Real.toNNReal (p.2*(p.1:ℝ))) y) :=
    ha.comp (ht2.prodMk continuous_const)
  exact ha.comp (ht1.prodMk (M.continuous.comp hY))

include hS hcontr in
theorem integrable (r : ℝ≥0) (y : E) : IntervalIntegrable (integrand S M r y) volume 0 1 := by
  exact ((joint_continuous S hS hcontr M y).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

include hcontr in
theorem integrand_bound (r : ℝ≥0) (y : E) (v : ℝ) : ‖integrand S M r y v‖ ≤ ‖M‖ * ‖y‖ :=
  (hcontr _ _).trans ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hcontr _ _) (norm_nonneg M)))

include hS hcontr in
def meanLinear (r : ℝ≥0) : E →ₗ[ℝ] E where
  toFun y := ∫ v in (0:ℝ)..1, integrand S M r y v
  map_add' y z := by
    simp only [integrand,map_add]
    exact intervalIntegral.integral_add (integrable S hS hcontr M r y) (integrable S hS hcontr M r z)
  map_smul' c y := by
    simp only [integrand,map_smul]
    exact intervalIntegral.integral_smul c _

include hS hcontr in
theorem mean_bound (r : ℝ≥0) (y : E) : ‖meanLinear S hS hcontr M r y‖ ≤ ‖M‖ * ‖y‖ := by
  change ‖∫ v in (0:ℝ)..1, integrand S M r y v‖ ≤ ‖M‖ * ‖y‖
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := integrand S M r y) (a := (0:ℝ)) (b := 1)
    (fun v _ => integrand_bound S hcontr M r y v)
  simpa only [sub_zero,abs_one,mul_one] using hh

include hS hcontr in
def covariance (r : ℝ≥0) : E →L[ℝ] E :=
  (meanLinear S hS hcontr M r).mkContinuous ‖M‖ (mean_bound S hS hcontr M r)

include hS hcontr in
theorem covariance_apply (r : ℝ≥0) (y : E) : covariance S hS hcontr M r y =
    ∫ v in (0:ℝ)..1, extend S ((1-v)*(r:ℝ)) (M (extend S (v*(r:ℝ)) y)) := rfl

include hS hcontr in
theorem covariance_norm (r : ℝ≥0) : ‖covariance S hS hcontr M r‖ ≤ ‖M‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg M) _

include hS hcontr in
theorem covariance_continuous (y : E) : Continuous (fun r => covariance S hS hcontr M r y) := by
  have hc := continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ))
    (f := fun r v => integrand S M r y v) (joint_continuous S hS hcontr M y)
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
  convert hc using 1
  funext r
  rw [covariance_apply,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_Icc_eq_integral_Ioc]
  rfl

include hS hcontr in
theorem covariance_zero (hzero : S 0 = ContinuousLinearMap.id ℝ E) (y : E) :
    covariance S hS hcontr M 0 y = M y := by
  rw [covariance_apply]
  simp [HeatIntervalCovariance.extend,hzero]

end HeatCovarianceOperator
#check @HeatCovarianceOperator.joint_continuous
#print axioms HeatCovarianceOperator.joint_continuous
#check @HeatCovarianceOperator.integrable
#print axioms HeatCovarianceOperator.integrable
#check @HeatCovarianceOperator.integrand_bound
#print axioms HeatCovarianceOperator.integrand_bound
#check @HeatCovarianceOperator.mean_bound
#print axioms HeatCovarianceOperator.mean_bound
#check @HeatCovarianceOperator.covariance_apply
#print axioms HeatCovarianceOperator.covariance_apply
#check @HeatCovarianceOperator.covariance_norm
#print axioms HeatCovarianceOperator.covariance_norm
#check @HeatCovarianceOperator.covariance_continuous
#print axioms HeatCovarianceOperator.covariance_continuous
#check @HeatCovarianceOperator.covariance_zero
#print axioms HeatCovarianceOperator.covariance_zero
