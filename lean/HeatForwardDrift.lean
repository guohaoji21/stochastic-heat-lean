import HeatBochnerCellPairing
import HeatPredictableSemigroup

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatForwardDrift
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

def kernel (f : ℝ≥0 × Ω → E) (b : ℝ≥0) (p : ℝ≥0 × Ω) : E := S (b-p.1) (f p)

include hS hcontr in
theorem kernel_measurable (f : ℝ≥0 × Ω → E) (hf : Measurable f) (b : ℝ≥0) :
    Measurable (kernel S f b) :=
  (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
    ((measurable_const.sub measurable_fst).prodMk hf)

include hS hcontr in
theorem kernel_memLp (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H)) (b : ℝ≥0) :
    MemLp (kernel S f b) 2 (energyMeasure μ H) :=
  hfm.norm.mono' (kernel_measurable S hS hcontr f hf b).stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall (fun p => hcontr _ _))

def value (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H)) (a b : ℝ≥0) : Lp E 2 μ :=
  (HeatBochnerCell.square_integrable μ H (kernel S f b) (kernel_measurable S hS hcontr f hf b)
    (kernel_memLp μ H S hS hcontr f hf hfm b) a b).toLp (HeatBochnerCell.value H (kernel S f b) a b)

theorem value_ae (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H)) (a b : ℝ≥0) :
    value μ H S hS hcontr f hf hfm a b=ᵐ[μ] fun ω => ∫ s in Ioc a b, S (b-s) (f (s,ω)) ∂timeMeasure H :=
  (HeatBochnerCell.square_integrable μ H (kernel S f b) (kernel_measurable S hS hcontr f hf b)
    (kernel_memLp μ H S hS hcontr f hf hfm b) a b).coeFn_toLp

theorem pairing (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H)) (a b ε : ℝ≥0) (Z : Lp E 2 μ) :
    inner ℝ (value μ H S hS hcontr f hf hfm a b) (((S ε).compLpL 2 μ) Z)=
      ∫ p, (Ioc a b).indicator (fun s => inner ℝ (f (s,p.2)) (S (ε+(b-s)) (Z p.2))) p.1 ∂energyMeasure μ H := by
  have hh := HeatBochnerCellPairing.pairing μ H (kernel S f b) (kernel_measurable S hS hcontr f hf b)
    (kernel_memLp μ H S hS hcontr f hf hfm b) a b (((S ε).compLpL 2 μ) Z)
  change inner ℝ (value μ H S hS hcontr f hf hfm a b) (((S ε).compLpL 2 μ) Z)=_ at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae ((S ε).coeFn_compLpL Z)] with p hp
  by_cases ht : p.1∈Ioc a b
  · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht,hp]
    change inner ℝ (S (b-p.1) (f p)) (S ε (Z p.2))=_
    rw [hsym]
    have hs := congrArg (fun A : E →L[ℝ] E => A (Z p.2)) (hsem (b-p.1) ε)
    rw [add_comm (b-p.1) ε] at hs
    exact congrArg (fun z => inner ℝ (f p) z) hs.symm
  · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht]

end HeatForwardDrift
#check @HeatForwardDrift.kernel_measurable
#print axioms HeatForwardDrift.kernel_measurable
#check @HeatForwardDrift.kernel_memLp
#print axioms HeatForwardDrift.kernel_memLp
#check @HeatForwardDrift.value_ae
#print axioms HeatForwardDrift.value_ae
#check @HeatForwardDrift.pairing
#print HeatForwardDrift.pairing
#print axioms HeatForwardDrift.pairing
