import HeatCanonicalUsualCross56
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
noncomputable section
namespace HeatCanonicalSeparable
open MeasureTheory
open scoped NNReal

theorem completed_separable :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    IsSeparable HeatCanonicalUsualCross56.completedWiener := by
  have hp : @IsProbabilityMeasure C(ℝ≥0,ℝ) (borel C(ℝ≥0,ℝ)) HeatCanonicalWiener56.wienerMeasure :=
    HeatCanonicalWiener56.coordinate_preBrownian.isGaussianProcess.isProbabilityMeasure
  have hs : @IsSeparable C(ℝ≥0,ℝ) (borel C(ℝ≥0,ℝ)) HeatCanonicalWiener56.wienerMeasure := by
    letI := hp
    infer_instance
  letI := hs
  change IsSeparable HeatCanonicalWiener56.wienerMeasure.completion
  infer_instance

end HeatCanonicalSeparable
#check @HeatCanonicalSeparable.completed_separable
#print HeatCanonicalSeparable.completed_separable
#print axioms HeatCanonicalSeparable.completed_separable
