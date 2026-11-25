import HeatTorusReal
import HeatCanonicalNative
import HeatCountableBasis
import HeatTerminalNaturality

set_option autoImplicit false
noncomputable section

namespace HeatTorusCanonicalIto

open MeasureTheory SHE SHE.HilbertColumns HeatTorusReal
open scoped NNReal ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance (ι : Type*) [Fintype ι] : SecondCountableTopology (RealState ι) :=
  Lp.SecondCountableTopology
local instance (ι : Type*) [Fintype ι] : MeasurableSpace (RealState ι) := borel _
local instance (ι : Type*) [Fintype ι] : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure HeatCanonicalUsualCross56.completedWiener :=
  HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

def indices (ι : Type*) [Fintype ι] : Set (RealState ι) :=
  Classical.choose (HeatCountableBasis.exists_countable_hilbertBasis (E := RealState ι))

instance (ι : Type*) [Fintype ι] : Countable (indices ι) :=
  (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis
    (E := RealState ι))).1.to_subtype

def basis (ι : Type*) [Fintype ι] : HilbertBasis (indices ι) ℝ (RealState ι) :=
  Classical.choice (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis
    (E := RealState ι))).2

/-- Itô integration on the real torus using the canonical coordinate Brownian motion. -/
def integral (ι : Type*) [Fintype ι] (T : ℝ≥0) :
    StandardTerminalIto (C := RealState ι) (E := RealState ι)
      HeatCanonicalUsual56.usualFiltration HeatCanonicalUsualCross56.completedWiener T :=
  HeatTerminalNaturality.integral HeatCanonicalUsual56.usualFiltration
    HeatCanonicalUsualCross56.completedWiener T (basis ι) (HeatCanonicalNative.scalar T)

end HeatTorusCanonicalIto
