import HeatVersionLp
import Mathlib.Probability.Process.Adapted

set_option autoImplicit false
noncomputable section
namespace HeatFiniteHorizonLp
open MeasureTheory
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nontrivial E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem exists_version (X : ℝ≥0 → Ω → E) (hc : ∀ ω, Continuous (fun t => X t ω))
    (ha : StronglyAdapted F X) (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0≤D ω)
    (hb : ∀ t, t≤H → ∀ ω, ‖X t ω‖≤D ω) :
    ∃ V : ℝ≥0 → Lp E 2 μ, Continuous V ∧
      (∀ t, t≤H → V t=ᵐ[μ] X t) ∧
      (∀ t, AEStronglyMeasurable[F t] (V t) μ) := by
  let Y : ℝ≥0 → Ω → E := fun t ω => X (min t H) ω
  have hYa : StronglyAdapted F Y := fun t => (ha (min t H)).mono (F.mono (min_le_left t H))
  let hm : ∀ t, StronglyMeasurable (Y t) := fun t => (hYa t).mono (F.le t)
  have hYc (ω : Ω) : Continuous (fun t => Y t ω) :=
    (hc ω).comp (continuous_id.min continuous_const)
  have hB (t : ℝ≥0) (ω : Ω) : ‖Y t ω‖≤D ω := hb _ (min_le_right _ _) ω
  let V := HeatVersionLp.value μ Y hm D hD hB
  have hrep (t : ℝ≥0) : V t=ᵐ[μ] Y t := HeatVersionLp.value_ae μ Y hm D hD hB t
  refine ⟨V,HeatVersionLp.continuous μ Y hm D hD hD0 hB hYc,?_,?_⟩
  · intro t ht
    simpa only [Y,min_eq_left ht] using hrep t
  · intro t
    exact (hYa t).aestronglyMeasurable.congr (hrep t).symm

end HeatFiniteHorizonLp
#check @HeatFiniteHorizonLp.exists_version
#print HeatFiniteHorizonLp.exists_version
#print axioms HeatFiniteHorizonLp.exists_version
