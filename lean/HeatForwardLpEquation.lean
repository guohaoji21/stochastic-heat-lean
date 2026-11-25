import HeatControlledRestart
import HeatForwardDrift
import HeatLpIdentity

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace HeatForwardLpEquation
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem equation (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (g : E) (u : Process (E := E) F μ H) (V : ℝ≥0 → Lp E 2 μ)
    (hrep : ∀ t, V t=ᵐ[μ] fun ω => S t g+HeatControlConvolution.value H S f t ω+
      (I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω)
    {a b : ℝ≥0} (hab : a≤b) :
    V b=((S (b-a)).compLpL 2 μ) (V a)+HeatForwardDrift.value μ H S hS hcontr f hf hfm a b+
      (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u) := by
  have hr := HeatControlledRestart.restart F μ H S hS hcontr M hsem basis J f hf hfm g u V hrep hab
  apply HeatLpIdentity.add μ (S (b-a)) (V b) (V a) (HeatForwardDrift.value μ H S hS hcontr f hf hfm a b)
    ((I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u))
  filter_upwards [hr,HeatForwardDrift.value_ae μ H S hS hcontr f hf hfm a b] with ω hr hd
  rw [hd]
  exact hr

end HeatForwardLpEquation
#check @HeatForwardLpEquation.equation
#print HeatForwardLpEquation.equation
#print axioms HeatForwardLpEquation.equation
