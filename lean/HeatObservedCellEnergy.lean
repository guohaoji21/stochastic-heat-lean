import HeatQuadraticObservation

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatObservedCellEnergy
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem normalized (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0,s≤H → (J.integral (StoppedItoInputs.stop F μ H s R) : Ω → ℝ)=ᵐ[μ] W s)
    {a c : ℝ≥0} (hac : a≤c) (hcH : c≤H) (ζ : Ω → ℝ)
    (hζ : StronglyMeasurable[F a] ζ) (hζ2 : MemLp ζ 2 μ) (h : ℝ) (A D : E) :
    (∫ ω,‖(ζ ω/h) • ((W c ω-W a ω) • A+D)‖^2 ∂μ)=
      (h⁻¹)^2*(∫ ω,ζ ω^2 ∂μ)*(((c:ℝ)-(a:ℝ))*‖A‖^2+‖D‖^2) := by
  let X := fun ω => ζ ω*(W c ω-W a ω)
  have hX : MemLp X 2 μ := HeatWeightedBrownian.weighted_increment_memLp F μ H J hlocal W hW hac hcH ζ hζ hζ2
  have hsq : (∫ ω,X ω^2 ∂μ)=((c:ℝ)-(a:ℝ))*(∫ ω,ζ ω^2 ∂μ) :=
    HeatWeightedIncrementMoments.square F μ H J hlocal W hW hac hcH ζ hζ hζ2
  have hcross : (∫ ω,X ω*ζ ω ∂μ)=0 :=
    HeatWeightedIncrementMoments.cross F μ H J hlocal W hW hac hcH ζ hζ hζ2
  have he := HeatQuadraticObservation.expectation μ X ζ hX hζ2 h⁻¹ A D
  have hn : (fun ω => ‖(ζ ω/h) • ((W c ω-W a ω) • A+D)‖^2)=
      fun ω => ‖h⁻¹ • (X ω • A+ζ ω • D)‖^2 := by
    funext ω
    apply congrArg (fun z : E => ‖z‖^2)
    dsimp only [X]
    simp only [div_eq_mul_inv,smul_add,smul_smul]
    module
  rw [hn]
  rw [hsq,hcross] at he
  exact he.trans (by ring)

end HeatObservedCellEnergy
#check @HeatObservedCellEnergy.normalized
#print HeatObservedCellEnergy.normalized
#print axioms HeatObservedCellEnergy.normalized
