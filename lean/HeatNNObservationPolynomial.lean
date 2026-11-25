import HeatObservationPolynomial
import HeatIntervalCovariance
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
noncomputable section
namespace HeatNNObservationPolynomial
open MeasureTheory Set SHE.PredictableL2
open scoped NNReal ENNReal

def weight (a b s : ℝ≥0) : ℝ :=
  (((s:ℝ)-(a:ℝ))+((b:ℝ)-(s:ℝ))^2)/((b:ℝ)-(a:ℝ))^2

theorem integrable (H a b : ℝ≥0) : IntegrableOn (weight a b) (Ioc a b) (timeMeasure H) := by
  have hc : Continuous (weight a b) := by unfold weight;fun_prop
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem integral {H a b : ℝ≥0} (hab : a<b) (hbH : b ≤ H) :
    (∫ s in Ioc a b,weight a b s ∂timeMeasure H)=1/2+((b:ℝ)-(a:ℝ))/3 := by
  rw [timeMeasure_restrict_Ioc a hbH,HeatIntervalCovariance.interval_integral]
  have he : (∫ s in Ioc (a:ℝ) (b:ℝ),weight a b s.toNNReal)=
      ∫ s in Ioc (a:ℝ) (b:ℝ),((s-(a:ℝ))+((b:ℝ)-s)^2)/((b:ℝ)-(a:ℝ))^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 ≤ s := a.property.trans hs.1.le
    simp only [weight,Real.coe_toNNReal s hs0]
  rw [he,←intervalIntegral.integral_of_le (show (a:ℝ) ≤ (b:ℝ) by exact_mod_cast hab.le)]
  exact HeatObservationPolynomial.normalized _ _ (by exact_mod_cast hab)

end HeatNNObservationPolynomial
#check @HeatNNObservationPolynomial.integrable
#print axioms HeatNNObservationPolynomial.integrable
#check @HeatNNObservationPolynomial.integral
#print axioms HeatNNObservationPolynomial.integral
