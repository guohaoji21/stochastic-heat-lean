import SHE.IntervalTimeMeasure

set_option autoImplicit false
noncomputable section
namespace HeatCompactTimeIntegrability
open MeasureTheory Filter Set SHE.PredictableL2
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E]

theorem of_continuous (f : ℝ≥0 → E) (hf : Continuous f) (T : ℝ≥0) :
    Integrable f (timeMeasure T) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ≥0) T)).bddAbove_image hf.norm.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [timeMeasure_ae_mem T] with t ht
  exact hC (mem_image_of_mem (fun t => ‖f t‖) ⟨zero_le,ht.2⟩)

end HeatCompactTimeIntegrability
#check @HeatCompactTimeIntegrability.of_continuous
#print HeatCompactTimeIntegrability.of_continuous
#print axioms HeatCompactTimeIntegrability.of_continuous
