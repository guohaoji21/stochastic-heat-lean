import HeatCanonicalHeatMoments
import SHEStochastic.DirectHilbertBDG
import SHEStochastic.FiniteCylindricalParameterVersions

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatCanonicalNative
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate
local instance : MeasurableSpace C(ℝ≥0,ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

def family (H : ℝ≥0) : SHEStochastic.FiniteScalarIto.Family F μ H Unit :=
  ⟨⟨(fun _ => W),
    (fun _ t => (HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted t).measurable),
    (fun n a => HeatFilteredBrownianFiniteLaw.finite_law («μ» := μ)
      HeatCanonicalUsual56.coordinate_filtered_brownian H n a)⟩,
    (fun _ ω => ω.continuous)⟩

def scalar (H : ℝ≥0) : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H :=
  SHEStochastic.FiniteCylindricalIto.terminalIto (family H).toCoordinates HeatTerminalBrownian.e

theorem locality (H : ℝ≥0) : StandardTerminalPastLocality (scalar H) :=
  SHEStochastic.FiniteCylindricalIto.pastLocality (family H) HeatTerminalBrownian.e

theorem coordinate (H t : ℝ≥0) (ht : t≤H) :
    (scalar H).integral (StoppedItoInputs.stop F μ H t
      (RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ())) =ᵐ[μ] W t :=
  SHEStochastic.FiniteCylindricalIto.coordinate_integral (family H) HeatTerminalBrownian.e () t ht

theorem continuous_stopped (H : ℝ≥0) : SHEStochastic.ContinuousStoppedVersions (scalar H) :=
  SHEStochastic.FiniteCylindricalIto.continuousStoppedVersions (family H) HeatTerminalBrownian.e

end HeatCanonicalNative
#check @HeatCanonicalNative.locality
#print axioms HeatCanonicalNative.locality
#check @HeatCanonicalNative.coordinate
#print axioms HeatCanonicalNative.coordinate
#check @HeatCanonicalNative.continuous_stopped
#print axioms HeatCanonicalNative.continuous_stopped
