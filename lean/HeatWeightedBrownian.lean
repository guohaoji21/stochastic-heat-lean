import HeatWeightedCellInput
import HeatTerminalBrownian
import SHEStochastic.UnboundedPastMultiplier

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatWeightedBrownian
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem weighted_integral (hlocal : StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    {a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) :
    J.integral (HeatWeightedCellInput.constant F μ H a b C hC hCm (HeatTerminalBrownian.e ())) =ᵐ[μ]
      (fun ω => C ω*(W b ω-W a ω)) := by
  let V := HeatWeightedCellInput.constant F μ H a b C hC hCm (HeatTerminalBrownian.e ())
  have hv : V =ᵐ[energyMeasure μ H] (fun p => PredictableSteps.step a b C p • R p) := by
    filter_upwards [HeatWeightedCellInput.constant_ae F μ H a b C hC hCm (HeatTerminalBrownian.e ()),
      RotatedCylindricalCoordinates.constant_ae F μ H (HeatTerminalBrownian.e ())] with p hp hr
    rw [hp]
    change _ = PredictableSteps.step a b C p • RotatedCylindricalCoordinates.constant F μ H (HeatTerminalBrownian.e ()) p
    rw [hr]
  have hh := SHEStochastic.UnboundedPastMultiplier.cell J hlocal R V a b hab C hC hv
  filter_upwards [hh,hW b hbH,hW a (hab.trans hbH)] with ω hh hb ha
  exact hh.trans (by rw [hb,ha])

theorem weighted_increment_memLp (hlocal : StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    {a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) :
    MemLp (fun ω => C ω*(W b ω-W a ω)) 2 μ :=
  (Lp.memLp _).ae_eq (weighted_integral F μ H J hlocal W hW hab hbH C hC hCm)

end HeatWeightedBrownian
#check @HeatWeightedBrownian.weighted_integral
#print axioms HeatWeightedBrownian.weighted_integral
#check @HeatWeightedBrownian.weighted_increment_memLp
#print axioms HeatWeightedBrownian.weighted_increment_memLp
