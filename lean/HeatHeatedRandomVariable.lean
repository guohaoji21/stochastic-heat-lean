import HeatPredictableSemigroup
import SHE.PredictableL2

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatHeatedRandomVariable
open MeasureTheory Filter SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

include hS hcontr in
theorem square_integrable (r : ℝ≥0 → ℝ≥0) (hr : Measurable r) (Y : Lp E 2 μ) :
    MemLp (fun p : ℝ≥0 × Ω => S (r p.1) (Y p.2)) 2 (energyMeasure μ H) := by
  have hm : Measurable (fun p : ℝ≥0 × Ω => S (r p.1) (Y p.2)) :=
    (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
      ((hr.comp measurable_fst).prodMk ((Lp.stronglyMeasurable Y).measurable.comp measurable_snd))
  apply ((Lp.memLp Y).norm.comp_snd (timeMeasure H)).mono' hm.stronglyMeasurable.aestronglyMeasurable
  exact Eventually.of_forall (fun p => hcontr _ _)

end HeatHeatedRandomVariable
#check @HeatHeatedRandomVariable.square_integrable
#print HeatHeatedRandomVariable.square_integrable
#print axioms HeatHeatedRandomVariable.square_integrable
