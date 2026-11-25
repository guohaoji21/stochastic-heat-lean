import HeatBackwardKernel

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatBackwardKernelSplit
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)

include hS hcontr in
theorem input_split (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b) (u : Process (E := E) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    HeatBackwardKernel.input F μ H S hS hcontr M a b u =
      HeatBackwardKernel.input F μ H S hS hcontr M a c u +
        ((S (c-a)).compLpL 2 ν) (HeatBackwardKernel.input F μ H S hS hcontr M c b u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply PastItoAlgebra.eq_of_ambient_ae
  have hmap := ae_eq_of_ae_eq_trim ((S (c-a)).coeFn_compLpL (HeatBackwardKernel.input F μ H S hS hcontr M c b u))
  have hadd := ae_eq_of_ae_eq_trim (Lp.coeFn_add (HeatBackwardKernel.input F μ H S hS hcontr M a c u)
    (((S (c-a)).compLpL 2 ν) (HeatBackwardKernel.input F μ H S hS hcontr M c b u)))
  filter_upwards [HeatBackwardKernel.input_ae F μ H S hS hcontr M a b u,
    HeatBackwardKernel.input_ae F μ H S hS hcontr M a c u,
    HeatBackwardKernel.input_ae F μ H S hS hcontr M c b u,hmap,hadd] with p hab hac' hcb' hm ha
  rw [hab,ha]
  simp only [Pi.add_apply]
  rw [hm,hac',hcb']
  by_cases hp : a < p.1
  · by_cases hb : p.1 ≤ b
    · by_cases hc : p.1 ≤ c
      · have hnot : p.1 ∉ Ioc c b := fun h => not_lt_of_ge hc h.1
        simp [Set.indicator_of_mem (show p.1 ∈ Ioc a b from ⟨hp,hb⟩),
          Set.indicator_of_mem (show p.1 ∈ Ioc a c from ⟨hp,hc⟩),Set.indicator_of_notMem hnot]
      · have hcp : c < p.1 := lt_of_not_ge hc
        rw [Set.indicator_of_mem (show p.1 ∈ Ioc a b from ⟨hp,hb⟩),
          Set.indicator_of_notMem (show p.1 ∉ Ioc a c from fun h => hc h.2),
          Set.indicator_of_mem (show p.1 ∈ Ioc c b from ⟨hcp,hb⟩),zero_add]
        have ht : (c-a)+(p.1-c)=p.1-a := by
          rw [add_comm]
          exact tsub_add_tsub_cancel hcp.le hac
        have he := congrArg (fun A : E →L[ℝ] E => A (M (u p))) (hsem (c-a) (p.1-c))
        rw [ht] at he
        exact he
    · have hnab : p.1 ∉ Ioc a b := fun h => hb h.2
      have hnac : p.1 ∉ Ioc a c := fun h => hb (h.2.trans hcb)
      have hncb : p.1 ∉ Ioc c b := fun h => hb h.2
      simp [Set.indicator_of_notMem hnab,Set.indicator_of_notMem hnac,Set.indicator_of_notMem hncb]
  · have hnab : p.1 ∉ Ioc a b := fun h => hp h.1
    have hnac : p.1 ∉ Ioc a c := fun h => hp h.1
    have hncb : p.1 ∉ Ioc c b := fun h => hp (hac.trans_lt h.1)
    simp [Set.indicator_of_notMem hnab,Set.indicator_of_notMem hnac,Set.indicator_of_notMem hncb]

end HeatBackwardKernelSplit
#check @HeatBackwardKernelSplit.input_split
#print axioms HeatBackwardKernelSplit.input_split
