import HeatCanonicalVariationalForward

set_option autoImplicit false
noncomputable section
namespace HeatCanonicalPhysicalIto
open MeasureTheory SHE.PredictableL2 HeatIntervalNormalization
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0,ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩

def indices : Set Base := Classical.choose (HeatCountableBasis.exists_countable_hilbertBasis (E := Base))

instance countable_indices : Countable indices :=
  (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis (E := Base))).1.to_subtype

def basis : HilbertBasis indices ℝ Base :=
  Classical.choice (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis (E := Base))).2

def integral (T : ℝ≥0) : SHE.StandardTerminalIto (C := Base) (E := Base) F μ T :=
  HeatTerminalNaturality.integral F μ T basis (HeatCanonicalNative.scalar T)

end HeatCanonicalPhysicalIto
#check HeatCanonicalPhysicalIto.integral
#print HeatCanonicalPhysicalIto.integral
