import SHE.BieleckiKernel
import SHE.ConvolutionEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatRegularKernel
open MeasureTheory Set SHE SHE.PredictableL2
open scoped ENNReal NNReal

def kernel (γ u : ℝ) : ℝ≥0∞ := (Ioi (0 : ℝ)).indicator (fun u => ENNReal.ofReal (Real.exp (-2*γ*u))) u

def mass (γ : ℝ) : ℝ := 1/(2*γ)

theorem measurable (γ : ℝ) : Measurable (kernel γ) := by
  unfold kernel
  exact (ENNReal.continuous_ofReal.measurable.comp (by fun_prop)).indicator measurableSet_Ioi

theorem mass_nonneg (γ : ℝ) (hγ : 0 < γ) : 0 ≤ mass γ := by unfold mass; positivity

theorem kernel_mass (γ : ℝ) (hγ : 0 < γ) : (∫⁻ u : ℝ, kernel γ u) = ENNReal.ofReal (mass γ) := by
  have hi := integrableOn_exp_mul_Ioi (a := -2*γ) (by linarith) 0
  have he : (∫ u : ℝ in Ioi 0, Real.exp (-2*γ*u)) = mass γ := by
    rw [integral_exp_mul_Ioi (a := -2*γ) (by linarith) 0]
    simp only [mul_zero, Real.exp_zero, mass]
    ring
  unfold kernel
  rw [lintegral_indicator measurableSet_Ioi, ← ofReal_integral_eq_lintegral_ofReal hi, he]
  exact Filter.Eventually.of_forall fun u => (Real.exp_pos _).le

theorem causal_energy (H : ℝ≥0) (γ : ℝ) (hγ : 0 < γ) (F : ℝ≥0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, ∫⁻ s, kernel γ ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure t ∂timeMeasure H) ≤
      ENNReal.ofReal (mass γ) * (∫⁻ s, F s ∂timeMeasure H) := by
  have he : (∫⁻ t, ∫⁻ s, kernel γ ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure t ∂timeMeasure H) =
      ∫⁻ t in Ioc (0:ℝ) H, ∫⁻ s in Ioc (0:ℝ) t, kernel γ (t-s)*F s.toNNReal := by
    rw [timeMeasure_lintegral]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [timeMeasure_lintegral, Real.coe_toNNReal _ ht.1.le]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.coe_toNNReal _ hs.1.le]
  rw [he, timeMeasure_lintegral]
  have h := SHE.causal_convolution_energy_bound (kernel γ) (fun s => F s.toNNReal)
    (measurable γ) (hF.comp measurable_real_toNNReal) (H:ℝ)
  rw [kernel_mass γ hγ] at h
  exact h

end HeatRegularKernel
#check @HeatRegularKernel.measurable
#print axioms HeatRegularKernel.measurable
#check @HeatRegularKernel.mass_nonneg
#print axioms HeatRegularKernel.mass_nonneg
#check @HeatRegularKernel.kernel_mass
#print axioms HeatRegularKernel.kernel_mass
#check @HeatRegularKernel.causal_energy
#print axioms HeatRegularKernel.causal_energy
