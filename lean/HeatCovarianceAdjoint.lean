import HeatCovarianceOperator
import HeatPaperAdjoint
import HeatScalarMultiplier
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatCovarianceAdjoint
open MeasureTheory HeatCovarianceOperator
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

theorem point_pairing (hSsym : ∀ t x y, inner ℝ (S t x) y = inner ℝ x (S t y))
    (hMsym : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y)) (r : ℝ≥0) (v : ℝ) (x y : E) :
    inner ℝ (integrand S M r x v) y = inner ℝ x (integrand S M r y (1-v)) := by
  unfold integrand HeatIntervalCovariance.extend
  rw [hSsym,hMsym,hSsym,show 1-(1-v) = v by ring]

include hS hcontr in
theorem covariance_inner (hSsym : ∀ t x y, inner ℝ (S t x) y = inner ℝ x (S t y))
    (hMsym : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y)) (r : ℝ≥0) (x y : E) :
    inner ℝ (covariance S hS hcontr M r x) y = inner ℝ x (covariance S hS hcontr M r y) := by
  have h1 : inner ℝ (covariance S hS hcontr M r x) y =
      ∫ v in (0:ℝ)..1, inner ℝ (integrand S M r x v) y := by
    rw [real_inner_comm,covariance_apply]
    have hh := (innerSL ℝ y).intervalIntegral_comp_comm (integrable S hS hcontr M r x)
    change inner ℝ y (∫ v in (0:ℝ)..1, integrand S M r x v) = _
    simpa only [innerSL_apply_apply,real_inner_comm] using hh.symm
  have h2 := (innerSL ℝ x).intervalIntegral_comp_comm (integrable S hS hcontr M r y)
  rw [h1]
  simp_rw [point_pairing S M hSsym hMsym]
  have hr := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
    (fun v => inner ℝ x (integrand S M r y v)) 1
  norm_num only [sub_self,sub_zero] at hr
  rw [hr]
  exact h2

include hS hcontr in
theorem covariance_self_adjoint (hSsym : ∀ t x y, inner ℝ (S t x) y = inner ℝ x (S t y))
    (hMsym : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y)) (r : ℝ≥0) :
    (covariance S hS hcontr M r).adjoint = covariance S hS hcontr M r := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left,covariance_inner S hS hcontr M hSsym hMsym]

end HeatCovarianceAdjoint
#check @HeatCovarianceAdjoint.point_pairing
#print axioms HeatCovarianceAdjoint.point_pairing
#check @HeatCovarianceAdjoint.covariance_inner
#print axioms HeatCovarianceAdjoint.covariance_inner
#check @HeatCovarianceAdjoint.covariance_self_adjoint
#print axioms HeatCovarianceAdjoint.covariance_self_adjoint
