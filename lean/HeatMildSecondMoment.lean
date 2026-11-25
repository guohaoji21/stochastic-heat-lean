import HeatMildCovariance
import HeatIntervalCovariance

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatMildSecondMoment
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns HeatMildSolution
open scoped NNReal ENNReal

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
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

include hsem in
theorem second_moment (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0}
    (hab : a ≤ b) (hbH : b ≤ H) (g : E) (u : Process (E := E) F μ H)
    (hu : u = HeatVolterraForcing.orbit F μ H S hS hcontr g +
      HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u) :
    μ[(fun ω => (J.integral (StoppedItoInputs.stop F μ H b R) ω -
      J.integral (StoppedItoInputs.stop F μ H a R) ω) • value F μ H S hS hcontr M I g u b ω) | F a] =ᵐ[μ]
      (fun ω => ((b:ℝ)-(a:ℝ)) • ∫ v in (0:ℝ)..1,
        HeatIntervalCovariance.extend S ((1-v)*((b:ℝ)-(a:ℝ)))
          (M (HeatIntervalCovariance.extend S (v*((b:ℝ)-(a:ℝ)))
            (value F μ H S hS hcontr M I g u a ω)))) := by
  have hcross := HeatMildBrownianMoment.cross_bracket F μ H S hS hcontr M hsem basis J hlocal hab g u
  have hbracket := HeatMildCovariance.conditional_bracket S hS hcontr M F μ H hsem basis J hlocal (a := a) (b := b) g u hu
  have he := hcross.trans hbracket
  filter_upwards [he] with ω hω
  exact hω.trans (HeatIntervalCovariance.covariance_interval S M hab hbH
    (value F μ H S hS hcontr M I g u a ω))

end HeatMildSecondMoment
#check @HeatMildSecondMoment.second_moment
#print HeatMildSecondMoment.second_moment
#print axioms HeatMildSecondMoment.second_moment
