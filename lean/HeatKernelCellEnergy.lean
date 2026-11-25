import HeatMildKernelCross
import SHE.ProcessEnergy

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatKernelCellEnergy
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem bound (u v : Process (E := E) F μ H) (a b : ℝ≥0) (C : ℝ) (hC : 0≤C)
    (hv : ∀ᵐ p ∂energyMeasure μ H,
      ‖v p‖≤(Ioc a b).indicator (fun s => C*‖u (s,p.2)‖) p.1) :
    ‖v‖^2≤C^2*(∫ p, (Ioc a b).indicator (fun s => ‖u (s,p.2)‖^2) p.1 ∂energyMeasure μ H) := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hvLp := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  have hi : Integrable (fun p : ℝ≥0 × Ω => (Ioc a b).indicator (fun s => ‖u (s,p.2)‖^2) p.1) (energyMeasure μ H) :=
    hu.norm.integrable_sq.indicator (measurableSet_Ioc.preimage measurable_fst)
  rw [subsigma_norm_sq,← integral_const_mul]
  apply integral_mono_ae hvLp.norm.integrable_sq (hi.const_mul (C^2))
  filter_upwards [hv] with p hp
  by_cases ht : p.1∈Ioc a b
  · rw [Set.indicator_of_mem ht] at hp ⊢
    exact (pow_le_pow_left₀ (norm_nonneg _) hp 2).trans_eq (mul_pow _ _ _)
  · rw [Set.indicator_of_notMem ht] at hp ⊢
    have hz : ‖v p‖=0 := le_antisymm hp (norm_nonneg _)
    rw [hz,zero_pow (by omega : 2≠0),mul_zero]

end HeatKernelCellEnergy
#check @HeatKernelCellEnergy.bound
#print HeatKernelCellEnergy.bound
#print axioms HeatKernelCellEnergy.bound
