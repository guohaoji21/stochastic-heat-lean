import HeatPredictableLinearMap
import SHE.ProcessEnergy

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatSliceEnergy
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (u : Process (E := E) F μ H) (V : ℝ≥0 → Lp E 2 μ)
  (hV : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t) (A : E →L[ℝ] E)

include hV in
theorem norm_sq_slices :
    (fun t => ‖(A.compLpL 2 μ) (V t)‖^2)=ᵐ[timeMeasure H] fun t => ∫ ω,‖A (u (t,ω))‖^2 ∂μ := by
  filter_upwards [hV] with t ht
  rw [realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLpL (V t),ht] with ω ha hv
  rw [ha,←hv]

theorem raw_integrable : Integrable (fun p => ‖A (u p)‖^2) (energyMeasure μ H) := by
  have hi := (memLp_of_memLp_trim (predictable_le_product F)
    (Lp.memLp (HeatPredictableLinearMap.map F μ H A u))).norm.integrable_sq
  exact hi.congr ((HeatPredictableLinearMap.map_ae F μ H A u).fun_comp (fun x : E => ‖x‖^2))

include hV in
theorem integrable : Integrable (fun t => ‖(A.compLpL 2 μ) (V t)‖^2) (timeMeasure H) :=
  (raw_integrable F μ H u A).integral_prod_left.congr (norm_sq_slices F μ H u V hV A).symm

include hV in
theorem energy : (∫ t,‖(A.compLpL 2 μ) (V t)‖^2 ∂timeMeasure H)=
    ‖HeatPredictableLinearMap.map F μ H A u‖^2 := by
  rw [integral_congr_ae (norm_sq_slices F μ H u V hV A),
    subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F)]
  calc
    _ = ∫ p,‖A (u p)‖^2 ∂energyMeasure μ H := (integral_prod _ (raw_integrable F μ H u A)).symm
    _ = _ := integral_congr_ae (by
      filter_upwards [HeatPredictableLinearMap.map_ae F μ H A u] with p hp
      exact congrArg (fun x : E => ‖x‖^2) hp.symm)

end HeatSliceEnergy
#check @HeatSliceEnergy.norm_sq_slices
#print axioms HeatSliceEnergy.norm_sq_slices
#check @HeatSliceEnergy.raw_integrable
#print axioms HeatSliceEnergy.raw_integrable
#check @HeatSliceEnergy.integrable
#print axioms HeatSliceEnergy.integrable
#check @HeatSliceEnergy.energy
#print HeatSliceEnergy.energy
#print axioms HeatSliceEnergy.energy
