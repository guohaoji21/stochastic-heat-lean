import SHE.IntervalTimeMeasure

set_option autoImplicit false
noncomputable section
namespace HeatCellMass
open MeasureTheory SHE.PredictableL2 Set
open scoped NNReal ENNReal

theorem mass {H a b : ℝ≥0} (hab : a≤b) (hb : b≤H) :
    ((timeMeasure H).restrict (Ioc a b)).real univ=(b:ℝ)-(a:ℝ) := by
  rw [timeMeasure_restrict_Ioc a hb,Measure.real]
  have hm := congrArg (fun ν : Measure ℝ => ν univ) (intervalTimeMeasure_map a b)
  rw [Measure.map_apply measurable_coe_nnreal_real MeasurableSet.univ] at hm
  simp only [preimage_univ,Measure.restrict_apply_univ,Real.volume_Ioc] at hm
  rw [hm,ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hab))]

end HeatCellMass
#check @HeatCellMass.mass
#print HeatCellMass.mass
#print axioms HeatCellMass.mass
