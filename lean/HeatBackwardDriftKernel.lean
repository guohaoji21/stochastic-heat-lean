import HeatBackwardKernel
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatBackwardDriftKernel
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

def value (a b : ℝ≥0) (u : Process (E := E) F μ H) (ω : Ω) : E :=
  ∫ s in Ioc a b, S (s-a) (M (u (s,ω))) ∂timeMeasure H

include hS hcontr in
theorem factor_integrable (a : ℝ≥0) (u : Process (E := E) F μ H) :
    Integrable (fun p : ℝ≥0 × Ω => S (p.1-a) (M (u p))) (energyMeasure μ H) := by
  letI : IsFiniteMeasure (energyMeasure μ H) := by dsimp [energyMeasure]; infer_instance
  exact (memLp_of_memLp_trim (predictable_le_product F)
    (HeatBackwardKernel.factor_memLp F μ H S hS hcontr M a u)).integrable one_le_two

include hS hcontr in
theorem time_integrable (a : ℝ≥0) (u : Process (E := E) F μ H) :
    ∀ᵐ ω ∂μ, Integrable (fun s => S (s-a) (M (u (s,ω)))) (timeMeasure H) :=
  (factor_integrable F μ H S hS hcontr M a u).prod_left_ae

include hS hcontr in
theorem split (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b) (u : Process (E := E) F μ H) :
    value F μ H S M a b u =ᵐ[μ] (fun ω => value F μ H S M a c u ω +
      S (c-a) (value F μ H S M c b u ω)) := by
  filter_upwards [time_integrable F μ H S hS hcontr M a u,
    time_integrable F μ H S hS hcontr M c u] with ω ha hc
  unfold value
  rw [←Ioc_union_Ioc_eq_Ioc hac hcb,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc ha.integrableOn ha.integrableOn]
  congr 1
  calc
    _ = ∫ s in Ioc c b, S (c-a) (S (s-c) (M (u (s,ω)))) ∂timeMeasure H := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have ht : (c-a)+(s-c)=s-a := by rw [add_comm]; exact tsub_add_tsub_cancel hs.1.le hac
      have he := congrArg (fun A : E →L[ℝ] E => A (M (u (s,ω)))) (hsem (c-a) (s-c))
      rw [ht] at he
      exact he
    _ = _ := (S (c-a)).integral_comp_comm hc.integrableOn

end HeatBackwardDriftKernel
#check @HeatBackwardDriftKernel.factor_integrable
#print axioms HeatBackwardDriftKernel.factor_integrable
#check @HeatBackwardDriftKernel.time_integrable
#print axioms HeatBackwardDriftKernel.time_integrable
#check @HeatBackwardDriftKernel.split
#print axioms HeatBackwardDriftKernel.split
