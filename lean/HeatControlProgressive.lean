import HeatFiniteControlExtension
import HeatRestrictionAdjoint
import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp

set_option autoImplicit false
noncomputable section
namespace HeatControlProgressive
open MeasureTheory Set HeatRestrictionAdjoint
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
abbrev Control := Lp ℝ 2 paperControlMeasure
local instance : MeasurableSpace Control := borel Control
local instance : BorelSpace Control := ⟨rfl⟩
local instance : IsSeparable paperControlMeasure := by unfold paperControlMeasure paperDomainMeasure;infer_instance
local instance : SecondCountableTopology Control := Lp.SecondCountableTopology

variable {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (U : ℝ≥0 → Ω → Control)

theorem original_iff_strong :
    (∀ t : ℝ≥0, t≤T → Measurable[(inferInstance : MeasurableSpace (Iic t)).prod (F t)]
      (fun p : Iic t × Ω => U p.1 p.2)) ↔ HeatFiniteControlExtension.LocallyProgressive F T U := by
  constructor
  · intro h t ht
    exact (h t ht).stronglyMeasurable
  · intro h t ht
    exact (h t ht).measurable

end HeatControlProgressive
#check @HeatControlProgressive.original_iff_strong
#print HeatControlProgressive.original_iff_strong
#print axioms HeatControlProgressive.original_iff_strong
