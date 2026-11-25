import SHE.StoppedItoInputs
import SHE.ProcessEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatStoppedProcessBound
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

theorem square (u v : Process (E := E) F μ H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ p ∂energyMeasure μ H,‖u p‖ ≤ C*‖v p‖) (T : ℝ≥0) :
    ‖StoppedItoInputs.stop F μ H T u‖^2 ≤ C^2*‖StoppedItoInputs.stop F μ H T v‖^2 := by
  let U := StoppedItoInputs.stop F μ H T u
  let V := StoppedItoInputs.stop F μ H T v
  have hU : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp U)).norm.integrable_sq
  have hV : Integrable (fun p => ‖V p‖^2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp V)).norm.integrable_sq
  have hp : ∀ᵐ p ∂energyMeasure μ H,‖U p‖^2 ≤ C^2*‖V p‖^2 := by
    filter_upwards [hbound,StoppedItoInputs.stop_ae F μ H T u,StoppedItoInputs.stop_ae F μ H T v] with p hb hu hv
    rw [hu,hv]
    by_cases hs : p∈StoppedItoInputs.before (T:ℝ)
    · rw [Set.indicator_of_mem hs,Set.indicator_of_mem hs]
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
    · rw [Set.indicator_of_notMem hs,Set.indicator_of_notMem hs,norm_zero]
      simp
  have hi := integral_mono_ae hU (hV.const_mul (C^2)) hp
  rw [integral_const_mul] at hi
  rw [subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F),
    subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F)]
  exact hi

end HeatStoppedProcessBound
#check @HeatStoppedProcessBound.square
#print axioms HeatStoppedProcessBound.square
