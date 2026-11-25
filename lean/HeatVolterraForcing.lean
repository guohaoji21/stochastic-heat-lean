import HeatPredictableStateInput

set_option autoImplicit false
noncomputable section
namespace HeatVolterraForcing
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)
include hS hcontr

local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance

theorem orbit_memLp (g : E) : @MemLp _ _ F.predictable _ _
    (fun p : ℝ≥0 × Ω => S p.1 g) 2 ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hm : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => S p.1 g) :=
    ((hS g).measurable.comp (PredictableClock.time_measurable F)).stronglyMeasurable
  apply MemLp.of_bound hm.aestronglyMeasurable ‖g‖
  exact Filter.Eventually.of_forall fun p => hcontr p.1 g

def orbit (g : E) : Process (E := E) F μ H :=
  (orbit_memLp F μ H S hS hcontr g).toLp (fun p => S p.1 g)

theorem orbit_ae (g : E) : orbit F μ H S hS hcontr g =ᵐ[energyMeasure μ H]
    (fun p : ℝ≥0 × Ω => S p.1 g) :=
  ae_eq_of_ae_eq_trim (orbit_memLp F μ H S hS hcontr g).coeFn_toLp

end HeatVolterraForcing
#check @HeatVolterraForcing.orbit_memLp
#print axioms HeatVolterraForcing.orbit_memLp
#check @HeatVolterraForcing.orbit_ae
#print axioms HeatVolterraForcing.orbit_ae
