import HeatBackwardKernel
import HeatHilbertCross

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatMildKernelCross
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

def forward (a b : ℝ≥0) (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  PastItoInputs.post F μ H a (StoppedItoInputs.stop F μ H b
    (HeatPredictableStateInput.factor F μ H S hS hcontr M b u))

theorem forward_ae (a b : ℝ≥0) (u : Process (E := E) F μ H) :
    forward F μ H S hS hcontr M a b u=ᵐ[energyMeasure μ H]
      fun p => (Ioc a b).indicator (fun s => S (b-s) (M (u (s,p.2)))) p.1 := by
  have hn : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1≠b :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne b)
  filter_upwards [PastItoInputs.post_ae F μ H a (StoppedItoInputs.stop F μ H b
    (HeatPredictableStateInput.factor F μ H S hS hcontr M b u)),
    StoppedItoInputs.stop_ae F μ H b (HeatPredictableStateInput.factor F μ H S hS hcontr M b u),
    HeatPredictableStateInput.factor_ae F μ H S hS hcontr M b u,hn] with p hp hs hf hn
  change PastItoInputs.post F μ H a _ p=_
  rw [hp]
  by_cases ha : a<p.1 <;> by_cases hb : p.1<b
  · have hm : p.1∈Ioc a b := ⟨ha,hb.le⟩
    rw [if_pos ha,hs,Set.indicator_of_mem (show p∈StoppedItoInputs.before (b:ℝ) from hb),hf,Set.indicator_of_mem hm]
  · have hm : p.1∉Ioc a b := fun h => hn (le_antisymm h.2 (le_of_not_gt hb))
    rw [if_pos ha,hs,Set.indicator_of_notMem (show p∉StoppedItoInputs.before (b:ℝ) from hb),Set.indicator_of_notMem hm]
  · have hm : p.1∉Ioc a b := fun h => ha h.1
    rw [if_neg ha,Set.indicator_of_notMem hm]
  · have hm : p.1∉Ioc a b := fun h => ha h.1
    rw [if_neg ha,Set.indicator_of_notMem hm]

include hS hcontr in
theorem cross (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    {a b : ℝ≥0} (hab : a≤b) (u v : Process (E := E) F μ H) :
    inner ℝ (forward F μ H S hS hcontr M a b u)
      (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v)=
      ∫ p, (Ioc a b).indicator (fun s => inner ℝ (M (u (s,p.2))) (S (b-a) (v (s,p.2)))) p.1 ∂energyMeasure μ H := by
  let U := forward F μ H S hS hcontr M a b u
  let V := HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v
  have hm : StronglyMeasurable[F.predictable] (fun p => inner ℝ (U p) (V p)) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (Lp.stronglyMeasurable U).inner (Lp.stronglyMeasurable V)
  rw [L2.inner_def,← integral_trim (predictable_le_product F) hm]
  apply integral_congr_ae
  filter_upwards [forward_ae F μ H S hS hcontr M a b u,
    HeatBackwardKernel.input_ae F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v] with p hu hv
  rw [hu,hv]
  by_cases hp : p.1∈Ioc a b
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,Set.indicator_of_mem hp]
    simp only [ContinuousLinearMap.id_apply]
    rw [hsym]
    have ht : b-p.1+(p.1-a)=b-a := tsub_add_tsub_cancel hp.2 hp.1.le
    have he := congrArg (fun A : E →L[ℝ] E => A (v p)) (hsem (b-p.1) (p.1-a))
    rw [ht] at he
    exact congrArg (fun z => inner ℝ (M (u p)) z) he.symm
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,Set.indicator_of_notMem hp]
    simp

end HeatMildKernelCross
#check @HeatMildKernelCross.forward_ae
#print axioms HeatMildKernelCross.forward_ae
#check @HeatMildKernelCross.cross
#print HeatMildKernelCross.cross
#print axioms HeatMildKernelCross.cross
