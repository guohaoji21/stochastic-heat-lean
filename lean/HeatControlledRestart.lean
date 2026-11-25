import HeatControlRestart
import HeatMildRestart
import HeatMildKernelCross

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatControlledRestart
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

include hsem in
theorem restart (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (g : E) (u : Process (E := E) F μ H) (V : ℝ≥0 → Lp E 2 μ)
    (hrep : ∀ t, V t=ᵐ[μ] fun ω => S t g+HeatControlConvolution.value H S f t ω+
      (I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω)
    {a b : ℝ≥0} (hab : a≤b) :
    V b=ᵐ[μ] fun ω => S (b-a) (V a ω)+
      (∫ s in Set.Ioc a b, S (b-s) (f (s,ω)) ∂timeMeasure H)+
      (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u) ω := by
  let Q := HeatMildSolution.value F μ H S hS hcontr M I g u
  have hQ (t : ℝ≥0) : V t=ᵐ[μ] fun ω => Q t ω+HeatControlConvolution.value H S f t ω := by
    filter_upwards [hrep t,Lp.coeFn_add (Lp.const 2 μ (S t g))
      ((I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)),Lp.coeFn_const 2 μ (S t g)] with ω hv hs hc
    change V t ω=(Lp.const 2 μ (S t g)+(I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)) ω+_
    rw [hs]
    simp only [Pi.add_apply,hc,Function.const_apply]
    rw [hv]
    abel
  have hrestart : Q b=((S (b-a)).compLpL 2 μ) (Q a)+
      (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u) := by
    dsimp only [Q]
    rw [HeatMildRestart.restart F μ H S hS hcontr M hsem basis J hab]
    rw [←map_sub,←PastItoAlgebra.post_stop_eq_sub F μ H a b hab]
    rfl
  have hD := HeatControlRestart.restart μ H S hS hcontr hsem f hf hfm hab
  filter_upwards [hQ a,hQ b,hD,Lp.coeFn_add (((S (b-a)).compLpL 2 μ) (Q a))
    ((I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u)),
    (S (b-a)).coeFn_compLpL (Q a)] with ω ha hb hd hs hm
  rw [ha,hb,hrestart,hs]
  simp only [Pi.add_apply]
  rw [hm,hd,map_add]
  abel

end HeatControlledRestart
#check @HeatControlledRestart.restart
#print HeatControlledRestart.restart
#print axioms HeatControlledRestart.restart
