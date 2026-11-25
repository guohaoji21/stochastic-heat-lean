import HeatWeakOrbit
import HeatPaperAdjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatWeakPairing
open MeasureTheory HeatIntervalNormalization HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal

theorem orbit_integrable (x : Base) (T : ℝ≥0) : Integrable (fun s => family s x) (SHE.PredictableL2.timeMeasure T) := by
  apply (integrable_const ‖x‖).mono' (family_continuous x).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => family_contraction s x)

theorem integrated_test (x φ ψ : Base) (hφ : weakLaplacian φ ψ) (T : ℝ≥0) :
    inner ℝ (family T x) φ-inner ℝ x φ=
      ∫ s,inner ℝ (family s x) ψ ∂SHE.PredictableL2.timeMeasure T := by
  have ho := HeatWeakOrbit.time_integral φ ψ hφ T
  have hi := integral_inner (𝕜 := ℝ) (orbit_integrable ψ T) x
  calc
    _ = inner ℝ x (family T φ-φ) := by
      rw [inner_sub_right]
      exact congrArg (fun r : ℝ => r-inner ℝ x φ) (HeatPaperAdjoint.paper_heat_inner T x φ)
    _ = inner ℝ x (∫ s,family s ψ ∂SHE.PredictableL2.timeMeasure T) := congrArg (inner ℝ x) ho
    _ = ∫ s,inner ℝ x (family s ψ) ∂SHE.PredictableL2.timeMeasure T := hi.symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun s =>
      (HeatPaperAdjoint.paper_heat_inner s x ψ).symm))

end HeatWeakPairing
#check @HeatWeakPairing.orbit_integrable
#print axioms HeatWeakPairing.orbit_integrable
#check @HeatWeakPairing.integrated_test
#print HeatWeakPairing.integrated_test
#print axioms HeatWeakPairing.integrated_test
