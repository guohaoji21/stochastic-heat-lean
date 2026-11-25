import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import HeatPredictableSemigroupEnergy
import HeatScalarMultiplier

set_option autoImplicit false
noncomputable section
namespace HeatDirichletInput
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

def spatialMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 10)
local instance : IsSeparable spatialMeasure := by
  unfold spatialMeasure
  infer_instance
abbrev H := Lp ℝ 2 spatialMeasure
local instance : MeasurableSpace H := borel H
local instance : BorelSpace H := ⟨rfl⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology H := Lp.SecondCountableTopology

/-- Concrete spatial state and diffusion multiplier. The heat-operator family
is still an explicit assumption and must be instantiated separately. -/
theorem exists_predictable_diffusion_input {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (T : ℝ≥0)
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b spatialMeasure)
    (hbound : ∀ᵐ x ∂spatialMeasure, ‖b x‖ ≤ 1)
    (S : ℝ≥0 → H →L[ℝ] H) (hS : ∀ x, Continuous (fun t => S t x))
    (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)
    (Y : ℝ≥0 → Ω → H) (ha : StronglyAdapted F Y)
    (hc : ∀ ω, Continuous (fun t => Y t ω))
    (hY : MemLp (fun p : ℝ≥0 × Ω => Y p.1 p.2) 2 (energyMeasure μ T)) :
    ∃ (M : H →L[ℝ] H) (v : Process (E := H) F μ T),
      ‖M‖ ≤ 1 ∧
      (∀ y : H, (fun x => M y x) =ᵐ[spatialMeasure] fun x => b x * y x) ∧
      v =ᵐ[energyMeasure μ T] fun p => S (T-p.1) (M (Y p.1 p.2)) := by
  obtain ⟨M,hM,hMb⟩ := HeatScalarMultiplier.exists_multiplier spatialMeasure b hb hbound
  have hm := HeatPredictableSemigroup.predictable_heat_integrand_memLp F μ T S hS hcontr M Y ha hc hY
  let v : Process (E := H) F μ T := hm.toLp _
  exact ⟨M,v,hM,hMb,ae_eq_of_ae_eq_trim hm.coeFn_toLp⟩

end HeatDirichletInput
#check @HeatDirichletInput.exists_predictable_diffusion_input
#print axioms HeatDirichletInput.exists_predictable_diffusion_input
