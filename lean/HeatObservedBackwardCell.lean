import HeatObservedCellEnergy
import HeatBackwardDrift

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatObservedBackwardCell
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns HeatCovarianceOperator
open scoped NNReal ENNReal
variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem expectation (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0,s ≤ H → (J.integral (StoppedItoInputs.stop F μ H s R) : Ω → ℝ)=ᵐ[μ] W s)
    (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x,Continuous (fun s => S s x))
    (hcontr : ∀ s x,‖S s x‖ ≤ ‖x‖) (M : E →L[ℝ] E) (L : E →L[ℝ] V)
    {a s c : ℝ≥0} (has : a ≤ s) (hsc : s ≤ c) (hcH : c ≤ H) (ζ : Ω → ℝ)
    (hζ : StronglyMeasurable[F a] ζ) (hζ2 : MemLp ζ 2 μ) (q : E) :
    (∫ ω,‖L ((ζ ω/((c:ℝ)-(a:ℝ))) • HeatBackwardCell.state H S M W a c q s ω)‖^2 ∂μ)=
      (((c:ℝ)-(a:ℝ))⁻¹)^2*(∫ ω,ζ ω^2 ∂μ)*
        (((s:ℝ)-(a:ℝ))*‖L (S (c-s) q)‖^2+
          ((c-s:ℝ≥0):ℝ)^2*‖L (covariance S hS hcontr M (c-s) q)‖^2) := by
  have he := HeatObservedCellEnergy.normalized F μ H J hlocal W hW has (hsc.trans hcH)
    ζ hζ hζ2 ((c:ℝ)-(a:ℝ)) (L (S (c-s) q))
    (((c-s:ℝ≥0):ℝ) • L (covariance S hS hcontr M (c-s) q))
  have hn : (fun ω => ‖L ((ζ ω/((c:ℝ)-(a:ℝ))) • HeatBackwardCell.state H S M W a c q s ω)‖^2)=
      fun ω => ‖(ζ ω/((c:ℝ)-(a:ℝ))) • ((W s ω-W a ω) • L (S (c-s) q)+
        ((c-s:ℝ≥0):ℝ) • L (covariance S hS hcontr M (c-s) q))‖^2 := by
    funext ω
    rw [map_smul,HeatBackwardCell.state,map_add,map_smul,
      HeatBackwardDrift.drift_covariance S hS hcontr M hsc hcH,map_smul]
  rw [hn]
  simpa only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,abs_of_nonneg (NNReal.zero_le_coe)] using he

end HeatObservedBackwardCell
#check @HeatObservedBackwardCell.expectation
#print axioms HeatObservedBackwardCell.expectation
