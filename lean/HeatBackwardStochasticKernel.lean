import HeatBackwardKernelSplit

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatBackwardStochasticKernel
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
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)

def value (a b : ℝ≥0) (u : Process (E := E) F μ H) : Lp E 2 μ :=
  (I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b u)

include hS hcontr in
theorem split (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b) (u : Process (E := E) F μ H) :
    value F μ H S hS hcontr basis J a b u =
      value F μ H S hS hcontr basis J a c u +
        ((S (c-a)).compLpL 2 μ) (value F μ H S hS hcontr basis J c b u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  unfold value
  rw [HeatBackwardKernelSplit.input_split F μ H S hS hcontr _ hsem hac hcb,map_add,
    ←HeatTerminalNaturality.commutes F μ H basis J]

include hS hcontr in
theorem split_ae (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b) (u : Process (E := E) F μ H) :
    value F μ H S hS hcontr basis J a b u =ᵐ[μ] (fun ω =>
      value F μ H S hS hcontr basis J a c u ω +
        S (c-a) (value F μ H S hS hcontr basis J c b u ω)) := by
  rw [split F μ H S hS hcontr basis J hsem hac hcb]
  filter_upwards [Lp.coeFn_add (value F μ H S hS hcontr basis J a c u)
      (((S (c-a)).compLpL 2 μ) (value F μ H S hS hcontr basis J c b u)),
    (S (c-a)).coeFn_compLpL (value F μ H S hS hcontr basis J c b u)] with ω ha hm
  rw [ha]
  simp only [Pi.add_apply,hm]

end HeatBackwardStochasticKernel
#check @HeatBackwardStochasticKernel.split
#print axioms HeatBackwardStochasticKernel.split
#check @HeatBackwardStochasticKernel.split_ae
#print axioms HeatBackwardStochasticKernel.split_ae
