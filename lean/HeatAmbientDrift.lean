import HeatBochnerCell
import HeatTimeRestriction

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatAmbientDrift
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def value (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H)) (T : ℝ≥0) : Lp E 2 μ :=
  (HeatBochnerCell.square_integrable μ H f hf hfm 0 T).toLp (HeatBochnerCell.value H f 0 T)

theorem value_ae (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    {T : ℝ≥0} (hT : T≤H) :
    value μ H f hf hfm T=ᵐ[μ] fun ω => ∫ s,f (s,ω) ∂timeMeasure T := by
  have he := (HeatBochnerCell.square_integrable μ H f hf hfm 0 T).coeFn_toLp
  change value μ H f hf hfm T=ᵐ[μ] HeatBochnerCell.value H f 0 T at he
  apply he.trans
  apply Eventually.of_forall
  intro ω
  unfold HeatBochnerCell.value
  rw [timeMeasure_restrict_Ioc 0 hT]
  rfl

end HeatAmbientDrift
#check @HeatAmbientDrift.value_ae
#print HeatAmbientDrift.value_ae
#print axioms HeatAmbientDrift.value_ae
