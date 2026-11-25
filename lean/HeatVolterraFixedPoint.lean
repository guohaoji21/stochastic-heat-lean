import HeatVolterraEnergy
import HeatRegularFixedPoint
import SHE.KernelItoLimit

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatVolterraFixedPoint
open MeasureTheory SHE SHE.PredictableL2 SHE.KernelItoLimit HeatVolterraKernel
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

def convolution (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  SHE.KernelItoLimit.convolution (HeatVolterraModel.model F μ H S hS hcontr M hsem) I u

theorem weighted_energy (γ : ℝ) (hγ : 0 < γ) (u v : Process (E := E) F μ H) :
    ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ)
      (convolution F μ H S hS hcontr M hsem I u-convolution F μ H S hS hcontr M hsem I v)‖^2) ≤
      ENNReal.ofReal (‖M‖^2*HeatRegularKernel.mass γ) *
        ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ) (u-v)‖^2) := by
  have hexp : 2*(-γ) = -2*γ := by ring
  have hright : ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ) (u-v)‖^2) =
      ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2) ∂μ ∂timeMeasure H := by
    rw [PredictableExponential.energy]
    simp only [hexp]
    have ha := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v))
    apply lintegral_congr_ae
    filter_upwards [ha] with s hs
    apply lintegral_congr_ae
    filter_upwards [hs] with ω hω
    rw [hω]
    rfl
  rw [hright]
  change ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ)
    (SHE.KernelItoLimit.convolution (HeatVolterraModel.model F μ H S hS hcontr M hsem) I u -
      SHE.KernelItoLimit.convolution (HeatVolterraModel.model F μ H S hS hcontr M hsem) I v)‖^2) ≤ _
  rw [SHEStochastic.KernelItoWeighted.difference_isometry]
  simp only [hexp]
  exact HeatVolterraEnergy.expected_energy μ H S hS hcontr M γ hγ u v
    (HeatVolterraModel.state_measurable F μ H S hS hcontr u)
    (HeatVolterraModel.state_measurable F μ H S hS hcontr v)

theorem exists_unique (forcing : Process (E := E) F μ H) :
    ∃! v : Process (E := E) F μ H, v = forcing + convolution F μ H S hS hcontr M hsem I v :=
  HeatRegularFixedPoint.exists_unique F μ H (convolution F μ H S hS hcontr M hsem I)
    (‖M‖^2) (sq_nonneg _) (weighted_energy F μ H S hS hcontr M hsem I) forcing

end HeatVolterraFixedPoint
#check @HeatVolterraFixedPoint.weighted_energy
#print axioms HeatVolterraFixedPoint.weighted_energy
#check @HeatVolterraFixedPoint.exists_unique
#print axioms HeatVolterraFixedPoint.exists_unique
