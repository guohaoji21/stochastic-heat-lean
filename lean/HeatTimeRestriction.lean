import HeatControlConvolution
import SHE.IntervalTimeMeasure

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatTimeRestriction
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal

theorem restrict_Iic {H T : ℝ≥0} (hT : T≤H) :
    (timeMeasure H).restrict (Iic T)=timeMeasure T := by
  have hs : Iic T=ᵐ[timeMeasure H] Ioc 0 T := by
    filter_upwards [timeMeasure_ae_mem H] with t ht
    simp only [mem_Iic,mem_Ioc,ht.1,true_and]
  rw [Measure.restrict_congr_set hs,timeMeasure_restrict_Ioc 0 hT]
  simp only [timeMeasure,intervalTimeMeasure,NNReal.coe_zero]

theorem restrict_Iio {H T : ℝ≥0} (hT : T≤H) :
    (timeMeasure H).restrict (Iio T)=timeMeasure T := by
  have hs : Iio T=ᵐ[timeMeasure H] Iic T := by
    filter_upwards [(timeMeasure H).ae_ne T] with t ht
    change (t<T)=(t≤T)
    apply propext
    exact ⟨fun h => h.le,fun h => lt_of_le_of_ne h ht⟩
  rw [Measure.restrict_congr_set hs,restrict_Iic hT]

theorem mono {H T : ℝ≥0} (hT : T≤H) : timeMeasure T≤timeMeasure H := by
  rw [←restrict_Iic hT]
  exact Measure.restrict_le_self

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem control_value (S : ℝ≥0 → E →L[ℝ] E) (f : ℝ≥0 × Ω → E)
    {H T t : ℝ≥0} (ht : t≤T) (hT : T≤H) (ω : Ω) :
    HeatControlConvolution.value H S f t ω=HeatControlConvolution.value T S f t ω := by
  unfold HeatControlConvolution.value HeatControlConvolution.raw HeatVolterraKernel.raw
  change (∫ s,(Iio t).indicator (fun s => S (t-s) (f (s,ω))) s ∂timeMeasure H)=
    (∫ s,(Iio t).indicator (fun s => S (t-s) (f (s,ω))) s ∂timeMeasure T)
  rw [integral_indicator measurableSet_Iio,integral_indicator measurableSet_Iio,
    restrict_Iio (ht.trans hT),restrict_Iio ht]

end HeatTimeRestriction
#check @HeatTimeRestriction.restrict_Iic
#print axioms HeatTimeRestriction.restrict_Iic
#check @HeatTimeRestriction.restrict_Iio
#print axioms HeatTimeRestriction.restrict_Iio
#check @HeatTimeRestriction.mono
#print axioms HeatTimeRestriction.mono
#check @HeatTimeRestriction.control_value
#print HeatTimeRestriction.control_value
#print axioms HeatTimeRestriction.control_value
