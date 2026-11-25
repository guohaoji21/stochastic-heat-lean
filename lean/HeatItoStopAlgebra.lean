import SHE.PastItoAlgebra
import SHE.StoppedItoInputs
import HeatDeterministicPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HeatItoStopAlgebra
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

theorem stop_min (a b : ℝ≥0) (u : Process (E := E) F μ H) :
    StoppedItoInputs.stop F μ H a (StoppedItoInputs.stop F μ H b u)=
      StoppedItoInputs.stop F μ H ((min a b : ℝ≥0):ℝ) u := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [StoppedItoInputs.stop_ae F μ H a (StoppedItoInputs.stop F μ H b u),
    StoppedItoInputs.stop_ae F μ H b u,StoppedItoInputs.stop_ae F μ H ((min a b : ℝ≥0):ℝ) u] with p h1 h2 h3
  rw [h1,h3]
  simp only [Set.indicator_apply,StoppedItoInputs.before,mem_setOf_eq,NNReal.coe_min,lt_min_iff]
  by_cases ha : (p.1:ℝ)<(a:ℝ)
  · simp only [ha,ite_true,true_and]
    rw [h2]
    rfl
  · simp [ha]

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]

theorem cumulative_indicator (ν : Measure ℝ≥0) (f : ℝ≥0 → A) (a b : ℝ≥0) :
    HeatDeterministicPairing.cumulative ν ((Iio b).indicator f) a=
      HeatDeterministicPairing.cumulative ν f (min a b) := by
  unfold HeatDeterministicPairing.cumulative
  rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,Iio_inter_Iio]
  rw [min_comm]

end HeatItoStopAlgebra
#check @HeatItoStopAlgebra.stop_min
#print axioms HeatItoStopAlgebra.stop_min
#check @HeatItoStopAlgebra.cumulative_indicator
#print axioms HeatItoStopAlgebra.cumulative_indicator
