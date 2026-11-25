import HeatPredictableStateInput
import HeatTerminalNaturality
import SHE.PastItoAlgebra

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatBackwardKernel
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
include hS hcontr

theorem factor_predictable (a : ℝ≥0) (u : Process (E := E) F μ H) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => S (p.1-a) (M (u p))) := by
  have ht := (PredictableClock.time_measurable F).sub_const a
  have hu := M.continuous.measurable.comp (Lp.stronglyMeasurable u).measurable
  exact ((HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp (ht.prodMk hu)).stronglyMeasurable

theorem factor_memLp (a : ℝ≥0) (u : Process (E := E) F μ H) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0 × Ω => S (p.1-a) (M (u p))) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  apply ((Lp.memLp u).norm.const_mul ‖M‖).mono' (factor_predictable F μ H S hS hcontr M a u).aestronglyMeasurable
  exact Eventually.of_forall fun p => (hcontr _ _).trans (M.le_opNorm _)

def factor (a : ℝ≥0) (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  (factor_memLp F μ H S hS hcontr M a u).toLp (fun p => S (p.1-a) (M (u p)))

theorem factor_ae (a : ℝ≥0) (u : Process (E := E) F μ H) :
    factor F μ H S hS hcontr M a u =ᵐ[energyMeasure μ H] (fun p : ℝ≥0 × Ω => S (p.1-a) (M (u p))) :=
  ae_eq_of_ae_eq_trim (factor_memLp F μ H S hS hcontr M a u).coeFn_toLp

def input (a b : ℝ≥0) (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  PastItoInputs.post F μ H a (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M a u))

theorem input_ae (a b : ℝ≥0) (u : Process (E := E) F μ H) :
    input F μ H S hS hcontr M a b u =ᵐ[energyMeasure μ H]
      (fun p => (Ioc a b).indicator (fun s => S (s-a) (M (u (s,p.2)))) p.1) := by
  have hn : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 ≠ b :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne b)
  filter_upwards [PastItoInputs.post_ae F μ H a
    (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M a u)),
    StoppedItoInputs.stop_ae F μ H b (factor F μ H S hS hcontr M a u),
    factor_ae F μ H S hS hcontr M a u,hn] with p hp hs hf hn
  change PastItoInputs.post F μ H a _ p = _
  rw [hp]
  by_cases ha : a < p.1 <;> by_cases hb : p.1 < b
  · have hm : p.1 ∈ Ioc a b := ⟨ha,hb.le⟩
    rw [if_pos ha,hs,Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (b:ℝ) from hb),hf,Set.indicator_of_mem hm]
  · have hm : p.1 ∉ Ioc a b := fun h => hn (le_antisymm h.2 (le_of_not_gt hb))
    rw [if_pos ha,hs,Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (b:ℝ) from hb),Set.indicator_of_notMem hm]
  · have hm : p.1 ∉ Ioc a b := fun h => ha h.1
    rw [if_neg ha,Set.indicator_of_notMem hm]
  · have hm : p.1 ∉ Ioc a b := fun h => ha h.1
    rw [if_neg ha,Set.indicator_of_notMem hm]

end HeatBackwardKernel
#check @HeatBackwardKernel.factor_predictable
#print axioms HeatBackwardKernel.factor_predictable
#check @HeatBackwardKernel.factor_memLp
#print axioms HeatBackwardKernel.factor_memLp
#check @HeatBackwardKernel.factor_ae
#print axioms HeatBackwardKernel.factor_ae
#check @HeatBackwardKernel.input_ae
#print axioms HeatBackwardKernel.input_ae
