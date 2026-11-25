import HeatKernelCellEnergy
import HeatBochnerCell
import HeatCellMass
import HeatBackwardDriftKernel

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatActualCellEnergy
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)

theorem forward (a b : ℝ≥0) (u : Process (E := E) F μ H) :
    ‖HeatMildKernelCross.forward F μ H S hS hcontr M a b u‖^2≤
      ‖M‖^2*(∫ p, (Ioc a b).indicator (fun s => ‖u (s,p.2)‖^2) p.1 ∂energyMeasure μ H) := by
  apply HeatKernelCellEnergy.bound F μ H u _ a b ‖M‖ (norm_nonneg _)
  filter_upwards [HeatMildKernelCross.forward_ae F μ H S hS hcontr M a b u] with p hp
  rw [hp]
  by_cases ht : p.1∈Ioc a b
  · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]
    exact (hcontr _ _).trans (M.le_opNorm _)
  · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,norm_zero]

theorem backward (a b : ℝ≥0) (u : Process (E := E) F μ H) :
    ‖HeatBackwardKernel.input F μ H S hS hcontr M a b u‖^2≤
      ‖M‖^2*(∫ p, (Ioc a b).indicator (fun s => ‖u (s,p.2)‖^2) p.1 ∂energyMeasure μ H) := by
  apply HeatKernelCellEnergy.bound F μ H u _ a b ‖M‖ (norm_nonneg _)
  filter_upwards [HeatBackwardKernel.input_ae F μ H S hS hcontr M a b u] with p hp
  rw [hp]
  by_cases ht : p.1∈Ioc a b
  · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]
    exact (hcontr _ _).trans (M.le_opNorm _)
  · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,norm_zero]

def drift (a b : ℝ≥0) (u : Process (E := E) F μ H) : Lp E 2 μ :=
  (HeatBochnerCell.square_integrable μ H (fun p => S (p.1-a) (M (u p)))
    ((HeatBackwardKernel.factor_predictable F μ H S hS hcontr M a u).mono (predictable_le_product F)).measurable
    (memLp_of_memLp_trim (predictable_le_product F) (HeatBackwardKernel.factor_memLp F μ H S hS hcontr M a u)) a b).toLp
      (HeatBochnerCell.value H (fun p => S (p.1-a) (M (u p))) a b)

theorem drift_ae (a b : ℝ≥0) (u : Process (E := E) F μ H) :
    drift F μ H S hS hcontr M a b u=ᵐ[μ] HeatBackwardDriftKernel.value F μ H S M a b u :=
  (HeatBochnerCell.square_integrable μ H (fun p => S (p.1-a) (M (u p)))
    ((HeatBackwardKernel.factor_predictable F μ H S hS hcontr M a u).mono (predictable_le_product F)).measurable
    (memLp_of_memLp_trim (predictable_le_product F) (HeatBackwardKernel.factor_memLp F μ H S hS hcontr M a u)) a b).coeFn_toLp

theorem drift_bound {a b : ℝ≥0} (hab : a≤b) (hbH : b≤H) (u : Process (E := E) F μ H) :
    ‖drift F μ H S hS hcontr M a b u‖^2≤
      ((b:ℝ)-(a:ℝ))*‖HeatBackwardKernel.input F μ H S hS hcontr M a b u‖^2 := by
  have he := HeatBochnerCell.energy μ H (fun p => S (p.1-a) (M (u p)))
    ((HeatBackwardKernel.factor_predictable F μ H S hS hcontr M a u).mono (predictable_le_product F)).measurable
    (memLp_of_memLp_trim (predictable_le_product F) (HeatBackwardKernel.factor_memLp F μ H S hS hcontr M a u)) a b
  change ‖drift F μ H S hS hcontr M a b u‖^2≤_ at he
  rw [HeatCellMass.mass hab hbH] at he
  have hnorm : ‖HeatBackwardKernel.input F μ H S hS hcontr M a b u‖^2=
      ∫ p, (Ioc a b).indicator (fun s => ‖S (s-a) (M (u (s,p.2)))‖^2) p.1 ∂energyMeasure μ H := by
    rw [subsigma_norm_sq]
    apply integral_congr_ae
    filter_upwards [HeatBackwardKernel.input_ae F μ H S hS hcontr M a b u] with p hp
    rw [hp]
    by_cases ht : p.1∈Ioc a b
    · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,norm_zero,zero_pow (by omega : 2≠0)]
  rw [hnorm]
  exact he

end HeatActualCellEnergy
#check @HeatActualCellEnergy.forward
#print axioms HeatActualCellEnergy.forward
#check @HeatActualCellEnergy.backward
#print axioms HeatActualCellEnergy.backward
#check @HeatActualCellEnergy.drift_ae
#print axioms HeatActualCellEnergy.drift_ae
#check @HeatActualCellEnergy.drift_bound
#print HeatActualCellEnergy.drift_bound
#print axioms HeatActualCellEnergy.drift_bound
