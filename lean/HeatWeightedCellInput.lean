import HeatPredictableStateInput
import SHE.PredictableSteps

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatWeightedCellInput
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H a b : ℝ≥0)
  (C : Ω → ℝ) (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ)

include hC hCm in
theorem vector_memLp (x : E) : MemLp (fun ω => C ω • x) 2 μ := by
  apply (hCm.norm.const_mul ‖x‖).mono' (((hC.mono (F.le a)).smul_const x).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ω => by rw [norm_smul]; exact le_of_eq (mul_comm _ _))

def constant (x : E) : Process (E := E) F μ H :=
  PredictableSteps.process F μ H a b (fun ω => C ω • x)
    (hC.smul_const x) (vector_memLp F μ a C hC hCm x)

theorem constant_ae (x : E) : constant F μ H a b C hC hCm x =ᵐ[energyMeasure μ H]
    (fun p => PredictableSteps.step a b C p • x) := by
  have hh := PredictableSteps.process_ae F μ H a b (fun ω => C ω • x)
    (hC.smul_const x) (vector_memLp F μ a C hC hCm x)
  filter_upwards [hh] with p hp
  change PredictableSteps.process F μ H a b _ _ _ p = _
  rw [hp]
  by_cases hm : p.1 ∈ Set.Ioc a b <;> simp [PredictableSteps.step,hm]

include hC in
theorem curve_measurable (h : ℝ≥0 → E) (hc : Continuous h) :
    StronglyMeasurable[F.predictable] (fun p => PredictableSteps.step a b C p • h p.1) :=
  (PredictableSteps.step_stronglyMeasurable F a b hC).smul
    (hc.measurable.comp (PredictableClock.time_measurable F)).stronglyMeasurable

include hC hCm in
theorem curve_memLp (h : ℝ≥0 → E) (hc : Continuous h) (B : ℝ) (hb : ∀ t, ‖h t‖ ≤ B) :
    @MemLp _ _ F.predictable _ _ (fun p => PredictableSteps.step a b C p • h p.1) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hs := PredictableSteps.step_memLp F μ H a b hC hCm
  apply (hs.norm.const_mul B).mono' (curve_measurable F a b C hC h hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hb p.1) (norm_nonneg _)).trans_eq (mul_comm _ _))

def curve (h : ℝ≥0 → E) (hc : Continuous h) (B : ℝ) (hb : ∀ t, ‖h t‖ ≤ B) : Process (E := E) F μ H :=
  (curve_memLp F μ H a b C hC hCm h hc B hb).toLp (fun p => PredictableSteps.step a b C p • h p.1)

theorem curve_ae (h : ℝ≥0 → E) (hc : Continuous h) (B : ℝ) (hb : ∀ t, ‖h t‖ ≤ B) :
    curve F μ H a b C hC hCm h hc B hb =ᵐ[energyMeasure μ H]
      (fun p => PredictableSteps.step a b C p • h p.1) :=
  ae_eq_of_ae_eq_trim (curve_memLp F μ H a b C hC hCm h hc B hb).coeFn_toLp

end HeatWeightedCellInput
#check @HeatWeightedCellInput.vector_memLp
#print axioms HeatWeightedCellInput.vector_memLp
#check @HeatWeightedCellInput.constant_ae
#print axioms HeatWeightedCellInput.constant_ae
#check @HeatWeightedCellInput.curve_measurable
#print axioms HeatWeightedCellInput.curve_measurable
#check @HeatWeightedCellInput.curve_memLp
#print axioms HeatWeightedCellInput.curve_memLp
#check @HeatWeightedCellInput.curve_ae
#print axioms HeatWeightedCellInput.curve_ae
