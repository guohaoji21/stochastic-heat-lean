import HeatBackwardStochasticKernel
import HeatBackwardDriftKernel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatBackwardZero
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)

theorem input_self (M : E →L[ℝ] E) (a : ℝ≥0) (u : Process (E := E) F μ H) :
    HeatBackwardKernel.input F μ H S hS hcontr M a a u=0 := by
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [HeatBackwardKernel.input_ae F μ H S hS hcontr M a a u,
    ae_eq_of_ae_eq_trim (Lp.coeFn_zero E 2 ((energyMeasure μ H).trim (predictable_le_product F)))] with p hp hz
  rw [hp,hz]
  simp

theorem noise_self (a : ℝ≥0) (u : Process (E := E) F μ H) :
    HeatBackwardStochasticKernel.value F μ H S hS hcontr basis J a a u=0 := by
  unfold HeatBackwardStochasticKernel.value
  rw [input_self,map_zero]

theorem drift_self (M : E →L[ℝ] E) (a : ℝ≥0) (u : Process (E := E) F μ H) :
    HeatBackwardDriftKernel.value F μ H S M a a u = (fun _ => 0) := by
  funext ω
  simp [HeatBackwardDriftKernel.value]

end HeatBackwardZero
#check @HeatBackwardZero.input_self
#print axioms HeatBackwardZero.input_self
#check @HeatBackwardZero.noise_self
#print axioms HeatBackwardZero.noise_self
#check @HeatBackwardZero.drift_self
#print axioms HeatBackwardZero.drift_self
