import HeatCanonicalUsualCross56
import HeatTerminalTransport
import HeatCountableBasis

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatCanonicalTerminal
open MeasureTheory HeatCompletedSpace56 SHE SHE.HilbertColumns
open scoped NNReal ENNReal
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem canonical_terminal_nonempty (T : ℝ≥0) :
    letI : MeasurableSpace C(ℝ≥0, ℝ) := completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    Nonempty (StandardTerminalIto (C := E) (E := E) F μ T) := by
  letI : MeasurableSpace C(ℝ≥0, ℝ) := completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : MeasurableSpace (Space Unit ℝ) := borel _
  letI : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
  obtain ⟨w,hw,⟨b⟩⟩ := HeatCountableBasis.exists_countable_hilbertBasis (E := E)
  letI : Countable w := hw.to_subtype
  let e : HilbertBasis Unit ℝ (Space Unit ℝ) := ⟨LinearIsometryEquiv.refl ℝ _⟩
  obtain ⟨J,_,_,_⟩ := HeatCanonicalUsualCross56.canonical_interval_cross T b e
  exact ⟨HeatTerminalTransport.fromUnitColumns F μ T (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J)⟩

end HeatCanonicalTerminal
#check @HeatCanonicalTerminal.canonical_terminal_nonempty
#print HeatCanonicalTerminal.canonical_terminal_nonempty
#print axioms HeatCanonicalTerminal.canonical_terminal_nonempty
