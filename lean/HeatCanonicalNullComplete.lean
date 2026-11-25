import HeatCanonicalNative
import SHE.NullCompleteFiltration

set_option autoImplicit false
noncomputable section
namespace HeatCanonicalNullComplete
open MeasureTheory SHE
open scoped NNReal

theorem contains_nulls :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    NullCompleteFiltration.ContainsNullSets HeatCanonicalUsual56.usualFiltration
      HeatCanonicalUsualCross56.completedWiener := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  intro t A hA
  exact HeatCanonicalUsual56.complete.measurableSet_of_null hA t

end HeatCanonicalNullComplete
#check @HeatCanonicalNullComplete.contains_nulls
#print axioms HeatCanonicalNullComplete.contains_nulls
