import HeatWeightedCellEnergy
import HeatWeightedBrownian

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
namespace HeatWeightedIncrementMoments
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem square (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
  (hW : ∀ t : ℝ≥0, t ≤ H → (J.integral (StoppedItoInputs.stop F μ H t R) : Ω → ℝ) =ᵐ[μ] W t)
  {a c : ℝ≥0} (hac : a≤c) (hcH : c≤H) (ζ : Ω → ℝ)
  (hζ : StronglyMeasurable[F a] ζ) (hζ2 : MemLp ζ 2 μ)
 : (∫ ω,(ζ ω*(W c ω-W a ω))^2 ∂μ)=((c:ℝ)-(a:ℝ))*(∫ ω,ζ ω^2 ∂μ) := by
  let V := HeatWeightedCellInput.constant F μ H a c ζ hζ hζ2 (HeatTerminalBrownian.e ())
  have hv := HeatWeightedBrownian.weighted_integral F μ H J hlocal W hW hac hcH ζ hζ hζ2
  have he : (∫ ω,(ζ ω*(W c ω-W a ω))^2 ∂μ)=‖J.integral V‖^2 := by
    rw [SHE.PredictableL2.realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hv] with ω hω
    change (ζ ω*(W c ω-W a ω))^2=‖J.integral V ω‖^2
    rw [hω,Real.norm_eq_abs,sq_abs]
  rw [he,J.integral.norm_map,HeatWeightedCellEnergy.norm_sq F μ H hac hcH ζ hζ hζ2,
    HeatTerminalBrownian.e.orthonormal.norm_eq_one,one_pow,mul_one]

theorem cross (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
  (hW : ∀ t : ℝ≥0, t ≤ H → (J.integral (StoppedItoInputs.stop F μ H t R) : Ω → ℝ) =ᵐ[μ] W t)
  {a c : ℝ≥0} (hac : a≤c) (hcH : c≤H) (ζ : Ω → ℝ)
  (hζ : StronglyMeasurable[F a] ζ) (hζ2 : MemLp ζ 2 μ)
 : (∫ ω,(ζ ω*(W c ω-W a ω))*ζ ω ∂μ)=0 := by
  let V := HeatWeightedCellInput.constant F μ H a c ζ hζ hζ2 (HeatTerminalBrownian.e ())
  let Z := hζ2.toLp ζ
  have hZ : AEStronglyMeasurable[F a] Z μ := ⟨ζ,hζ,hζ2.coeFn_toLp⟩
  have he := HeatPastPairing.future_orthogonal J hlocal a V Z hZ
  rw [HeatWeightedCellEnergy.post_eq F μ H ζ hζ hζ2] at he
  rw [L2.inner_def] at he
  have hv := HeatWeightedBrownian.weighted_integral F μ H J hlocal W hW hac hcH ζ hζ hζ2
  calc
    _ = ∫ ω,inner ℝ (J.integral V ω) (Z ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hv,hζ2.coeFn_toLp] with ω h1 h2
      change (ζ ω*(W c ω-W a ω))*ζ ω=inner ℝ (J.integral V ω) (Z ω)
      rw [h1,h2]
      simp only [Real.inner_apply]
    _ = 0 := he

end HeatWeightedIncrementMoments
#check @HeatWeightedIncrementMoments.square
#print axioms HeatWeightedIncrementMoments.square
#check @HeatWeightedIncrementMoments.cross
#print HeatWeightedIncrementMoments.cross
#print axioms HeatWeightedIncrementMoments.cross
