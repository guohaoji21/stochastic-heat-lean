import HeatShiftedBrownian
import HeatCanonicalBDG

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatShiftedNative
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (W : ℝ≥0 → Ω → ℝ) (hW : IsFilteredPreBrownian W F μ)
  (hWc : ∀ ω,Continuous (fun s => W s ω))
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

def family (a H : ℝ≥0) : SHEStochastic.FiniteScalarIto.Family (HeatShiftedBrownian.filtration F a) μ H Unit :=
  ⟨⟨(fun _ => HeatShiftedBrownian.process W a),
    (fun _ t => ((HeatShiftedBrownian.filtered hW a).stronglyAdapted t).measurable),
    (fun n t => HeatFilteredBrownianFiniteLaw.finite_law («μ» := μ) (HeatShiftedBrownian.filtered hW a) H n t)⟩,
    (fun _ ω => HeatShiftedBrownian.continuous W hWc a ω)⟩

def scalar (a H : ℝ≥0) : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ)
    (HeatShiftedBrownian.filtration F a) μ H :=
  SHEStochastic.FiniteCylindricalIto.terminalIto (family F μ W hW hWc a H).toCoordinates HeatTerminalBrownian.e

theorem locality (a H : ℝ≥0) : StandardTerminalPastLocality (scalar F μ W hW hWc a H) :=
  SHEStochastic.FiniteCylindricalIto.pastLocality (family F μ W hW hWc a H) HeatTerminalBrownian.e

theorem coordinate (a H t : ℝ≥0) (ht : t ≤ H) :
    (scalar F μ W hW hWc a H).integral
      (StoppedItoInputs.stop (HeatShiftedBrownian.filtration F a) μ H t
        (RawCylindricalCoordinates.row (HeatShiftedBrownian.filtration F a) μ H
          (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()))=ᵐ[μ] HeatShiftedBrownian.process W a t :=
  SHEStochastic.FiniteCylindricalIto.coordinate_integral (family F μ W hW hWc a H) HeatTerminalBrownian.e () t ht

theorem continuous_stopped (a H : ℝ≥0) : SHEStochastic.ContinuousStoppedVersions (scalar F μ W hW hWc a H) :=
  SHEStochastic.FiniteCylindricalIto.continuousStoppedVersions (family F μ W hW hWc a H) HeatTerminalBrownian.e

variable {κ E : Type*} [Countable κ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem hilbert_bdg (basis : HilbertBasis κ ℝ E) (a H : ℝ≥0) (k : ℕ) :
    StandardTerminalBDGPower (2^k)
      (HeatTerminalNaturality.integral (HeatShiftedBrownian.filtration F a) μ H basis (scalar F μ W hW hWc a H))
      (SHEStochastic.NativeScalarBDG.constant k) :=
  HeatTerminalBDG.transfer (HeatShiftedBrownian.filtration F a) μ H basis (scalar F μ W hW hWc a H) (2^k) _
    (SHEStochastic.DirectHilbertBDG.power_two (family F μ W hW hWc a H) HeatTerminalBrownian.e basis k)

end HeatShiftedNative
#check @HeatShiftedNative.locality
#print axioms HeatShiftedNative.locality
#check @HeatShiftedNative.coordinate
#print axioms HeatShiftedNative.coordinate
#check @HeatShiftedNative.continuous_stopped
#print axioms HeatShiftedNative.continuous_stopped
#check @HeatShiftedNative.hilbert_bdg
#print axioms HeatShiftedNative.hilbert_bdg
