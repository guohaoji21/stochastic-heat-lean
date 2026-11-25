import HeatMildSecondMoment
import HeatCovarianceOperator

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatContinuousMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem moments (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t≤H → J.integral (StoppedItoInputs.stop F μ H t R)=ᵐ[μ] W t)
    (g : E) (u : Process (E := E) F μ H)
    (hu : u=HeatVolterraForcing.orbit F μ H S hS hcontr g+
      HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u)
    (Y : ℝ≥0 → Ω → E)
    (hrep : ∀ t, t≤H → Y t=ᵐ[μ] HeatMildSolution.value F μ H S hS hcontr M I g u t)
    {a c : ℝ≥0} (hac : a≤c) (hcH : c≤H) :
    μ[Y c | F a]=ᵐ[μ] (fun ω => S (c-a) (Y a ω)) ∧
      μ[(fun ω => (W c ω-W a ω) • Y c ω) | F a]=ᵐ[μ]
        (fun ω => ((c:ℝ)-(a:ℝ)) • HeatCovarianceOperator.covariance S hS hcontr M (c-a) (Y a ω)) := by
  have hca := hrep c hcH
  have haa := hrep a (hac.trans hcH)
  constructor
  · exact (condExp_congr_ae (m:=F a) hca).trans
      ((HeatMildRestart.conditional_mean F μ H S hS hcontr M hsem basis J hlocal hac g u).trans
        (haa.fun_comp (fun x => S (c-a) x)).symm)
  · have he := HeatMildSecondMoment.second_moment F μ H S hS hcontr M hsem basis J hlocal hac hcH g u hu
    have hin : (fun ω => (W c ω-W a ω) • Y c ω)=ᵐ[μ]
        (fun ω => (J.integral (StoppedItoInputs.stop F μ H c R) ω-J.integral (StoppedItoInputs.stop F μ H a R) ω) •
          HeatMildSolution.value F μ H S hS hcontr M I g u c ω) := by
      filter_upwards [hW c hcH,hW a (hac.trans hcH),hca] with ω hc ha hy
      rw [hc,ha,hy]
    have hcov (x : E) : HeatCovarianceOperator.covariance S hS hcontr M (c-a) x =
        ∫ v in (0:ℝ)..1, HeatIntervalCovariance.extend S ((1-v)*((c:ℝ)-(a:ℝ)))
          (M (HeatIntervalCovariance.extend S (v*((c:ℝ)-(a:ℝ))) x)) := by
      rw [HeatCovarianceOperator.covariance_apply,NNReal.coe_sub hac]
    have hout := haa.fun_comp (fun x => ((c:ℝ)-(a:ℝ)) • HeatCovarianceOperator.covariance S hS hcontr M (c-a) x)
    have hh := (condExp_congr_ae (m:=F a) hin).trans he
    filter_upwards [hh,hout] with ω hh hout
    dsimp only [Function.comp_def] at hout
    exact hh.trans (by rw [←hcov,←hout])

end HeatContinuousMoments
#check @HeatContinuousMoments.moments
#print axioms HeatContinuousMoments.moments
