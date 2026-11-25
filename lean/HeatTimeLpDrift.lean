import HeatTimeLpField
import HeatAmbientDrift
import HeatDeterministicPairing
import SHE.LpIntegralFubini

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatTimeLpDrift
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (H : ℝ≥0) (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))

theorem integral_value {T : ℝ≥0} (hT : T≤H) :
    (∫ t,HeatTimeLpField.value μ f t ∂timeMeasure T)=HeatAmbientDrift.value μ H f hf hfm T := by
  letI : IsFiniteMeasure (energyMeasure μ T) := by unfold energyMeasure;infer_instance
  have hfmT : MemLp f 2 (energyMeasure μ T) :=
    hfm.mono_measure (Measure.prod_mono (HeatTimeRestriction.mono hT) le_rfl)
  have hInt := SHE.LpIntegralFubini.integral_ae μ (timeMeasure T) (HeatTimeLpField.value μ f)
    ((HeatTimeLpField.square_integrable μ f hf T hfmT).integrable (by norm_num)) f
    (hfmT.integrable (by norm_num)) (HeatTimeLpField.value_ae μ f hf T hfmT)
  apply Lp.ext
  exact hInt.trans (HeatAmbientDrift.value_ae μ H f hf hfm hT).symm

theorem cumulative_value {T : ℝ≥0} (hT : T≤H) :
    HeatDeterministicPairing.cumulative (timeMeasure H) (HeatTimeLpField.value μ f) T=
      HeatAmbientDrift.value μ H f hf hfm T := by
  unfold HeatDeterministicPairing.cumulative
  rw [HeatTimeRestriction.restrict_Iio hT]
  exact integral_value μ H f hf hfm hT

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

theorem adapted (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t,ω))) (t : ℝ≥0) :
    AEStronglyMeasurable[F t] (HeatTimeLpField.value μ f t) μ := by
  have hm : StronglyMeasurable[F t] (fun ω => HeatTimeLpField.raw μ f (t,ω)) := by
    by_cases ht : t∈HeatTimeLpField.good μ f
    · simpa only [HeatTimeLpField.raw,if_pos ht] using hfa t
    · simpa only [HeatTimeLpField.raw,if_neg ht] using
        (stronglyMeasurable_const : StronglyMeasurable[F t] (fun _ : Ω => (0:E)))
  exact hm.aestronglyMeasurable.congr (HeatTimeLpField.value_raw_ae μ f t).symm

end HeatTimeLpDrift
#check @HeatTimeLpDrift.integral_value
#print axioms HeatTimeLpDrift.integral_value
#check @HeatTimeLpDrift.cumulative_value
#print axioms HeatTimeLpDrift.cumulative_value
#check @HeatTimeLpDrift.adapted
#print HeatTimeLpDrift.adapted
#print axioms HeatTimeLpDrift.adapted
