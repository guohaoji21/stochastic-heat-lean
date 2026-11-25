import HeatIntervalNormalization
import HeatDirichletInput

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatConcreteSemigroupInput
open MeasureTheory SHE SHE.PredictableL2 HeatIntervalNormalization
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by
  unfold baseMeasure
  infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

def family (t : ℝ≥0) : Base →L[ℝ] Base := paperHeat t

theorem family_continuous (x : Base) : Continuous (fun t : ℝ≥0 => family t x) :=
  (paperHeat_continuous x).comp continuous_subtype_val

theorem family_contraction (t : ℝ≥0) (x : Base) : ‖family t x‖ ≤ ‖x‖ :=
  paperHeat_contraction t x

theorem concrete_diffusion_input {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (T : ℝ≥0)
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1)
    (Y : ℝ≥0 → Ω → Base) (ha : StronglyAdapted F Y)
    (hc : ∀ ω, Continuous (fun t => Y t ω))
    (hY : MemLp (fun p : ℝ≥0 × Ω => Y p.1 p.2) 2 (energyMeasure μ T)) :
    ∃ (M : Base →L[ℝ] Base) (v : Process (E := Base) F μ T),
      ‖M‖ ≤ 1 ∧
      (∀ y : Base, (fun x => M y x) =ᵐ[baseMeasure] fun x => b x * y x) ∧
      v =ᵐ[energyMeasure μ T] fun p => family (T-p.1) (M (Y p.1 p.2)) := by
  exact HeatDirichletInput.exists_predictable_diffusion_input F μ T b hb hbound
    family family_continuous family_contraction Y ha hc hY

end HeatConcreteSemigroupInput
#check @HeatConcreteSemigroupInput.family_continuous
#print axioms HeatConcreteSemigroupInput.family_continuous
#check @HeatConcreteSemigroupInput.family_contraction
#print axioms HeatConcreteSemigroupInput.family_contraction
#check @HeatConcreteSemigroupInput.concrete_diffusion_input
#print axioms HeatConcreteSemigroupInput.concrete_diffusion_input
