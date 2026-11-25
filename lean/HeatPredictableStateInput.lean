import HeatConcreteSemigroupInput
import SHE.PredictableClock

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatPredictableStateInput
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

include hS hcontr

theorem factor_predictable (t : ℝ≥0) (u : Process (E := E) F μ H) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => S (t-p.1) (M (u p))) := by
  have ht : Measurable[F.predictable] (fun p : ℝ≥0 × Ω => t-p.1) :=
    (HeatPredictableSemigroup.continuous_remaining t).measurable.comp (PredictableClock.time_measurable F)
  have hu : Measurable[F.predictable] (fun p : ℝ≥0 × Ω => M (u p)) :=
    M.continuous.measurable.comp (Lp.stronglyMeasurable u).measurable
  exact ((HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp (ht.prodMk hu)).stronglyMeasurable

theorem factor_memLp (t : ℝ≥0) (u : Process (E := E) F μ H) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0 × Ω => S (t-p.1) (M (u p))) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  apply ((Lp.memLp u).norm.const_mul ‖M‖).mono' (factor_predictable F μ H S hS hcontr M t u).aestronglyMeasurable
  filter_upwards [] with p
  exact (hcontr _ _).trans (M.le_opNorm _)

def factor (t : ℝ≥0) (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  (factor_memLp F μ H S hS hcontr M t u).toLp (fun p => S (t-p.1) (M (u p)))

theorem factor_ae (t : ℝ≥0) (u : Process (E := E) F μ H) :
    factor F μ H S hS hcontr M t u =ᵐ[energyMeasure μ H]
      (fun p : ℝ≥0 × Ω => S (t-p.1) (M (u p))) :=
  ae_eq_of_ae_eq_trim (factor_memLp F μ H S hS hcontr M t u).coeFn_toLp

end HeatPredictableStateInput
#check @HeatPredictableStateInput.factor_predictable
#print axioms HeatPredictableStateInput.factor_predictable
#check @HeatPredictableStateInput.factor_memLp
#print axioms HeatPredictableStateInput.factor_memLp
#check @HeatPredictableStateInput.factor_ae
#print axioms HeatPredictableStateInput.factor_ae
