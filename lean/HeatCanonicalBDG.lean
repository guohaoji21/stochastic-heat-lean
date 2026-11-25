import HeatCanonicalNative
import HeatTerminalBDG
import SHE.NullCompleteFiltration

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatCanonicalBDG
open MeasureTheory SHE SHE.HilbertColumns
open scoped NNReal ENNReal
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0,ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

variable {κ E : Type*} [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem hilbert_bdg (basis : HilbertBasis κ ℝ E) (H : ℝ≥0) (k : ℕ) :
    StandardTerminalBDGPower (2^k)
      (HeatTerminalNaturality.integral F μ H basis (HeatCanonicalNative.scalar H))
      (SHEStochastic.NativeScalarBDG.constant k) :=
  HeatTerminalBDG.transfer F μ H basis (HeatCanonicalNative.scalar H) (2^k) _
    (SHEStochastic.DirectHilbertBDG.power_two (HeatCanonicalNative.family H) HeatTerminalBrownian.e basis k)

end HeatCanonicalBDG
#check @HeatCanonicalBDG.hilbert_bdg
#print HeatCanonicalBDG.hilbert_bdg
#print axioms HeatCanonicalBDG.hilbert_bdg
