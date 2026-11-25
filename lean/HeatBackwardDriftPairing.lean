import HeatActualCellEnergy
import HeatBochnerCellPairing

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatBackwardDriftPairing
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)

theorem pairing (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (a b ε : ℝ≥0) (Y : Lp E 2 μ) (v : Process (E := E) F μ H) :
    inner ℝ (((S ε).compLpL 2 μ) Y) (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v)=
      ∫ p, (Ioc a b).indicator (fun s => inner ℝ (M (v (s,p.2))) (S (ε+(s-a)) (Y p.2))) p.1 ∂energyMeasure μ H := by
  have hf := ((HeatBackwardKernel.factor_predictable F μ H S hS hcontr M a v).mono (predictable_le_product F)).measurable
  have hfm := memLp_of_memLp_trim (predictable_le_product F) (HeatBackwardKernel.factor_memLp F μ H S hS hcontr M a v)
  have hh := HeatBochnerCellPairing.pairing μ H (fun p => S (p.1-a) (M (v p))) hf hfm a b (((S ε).compLpL 2 μ) Y)
  change inner ℝ (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v) (((S ε).compLpL 2 μ) Y)=_ at hh
  calc
    _ = inner ℝ (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v) (((S ε).compLpL 2 μ) Y) := real_inner_comm _ _
    _ = _ := hh.trans (by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae ((S ε).coeFn_compLpL Y)] with p hp
      by_cases ht : p.1∈Ioc a b
      · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht,hp]
        rw [hsym]
        have he := congrArg (fun A : E →L[ℝ] E => A (Y p.2)) (hsem (p.1-a) ε)
        rw [add_comm (p.1-a) ε] at he
        exact congrArg (fun z => inner ℝ (M (v p)) z) he.symm
      · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht])

end HeatBackwardDriftPairing
#check @HeatBackwardDriftPairing.pairing
#print HeatBackwardDriftPairing.pairing
#print axioms HeatBackwardDriftPairing.pairing
