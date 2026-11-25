import HeatVersionLp
import HeatPathObservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatWeakEnergyPathValues
open MeasureTheory Filter Set SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem exists_continuous_values (X : ℝ≥0 → Ω → E) (hc : ∀ ω,Continuous (fun t => X t ω))
    (ha : StronglyAdapted F X)
    (hmax : Integrable (fun ω => HeatPathMaximum.value H X ω^2) μ) :
    ∃ V : ℝ≥0 → Lp E 2 μ,Continuous V ∧
      (∀ t,t ≤ H → V t=ᵐ[μ] X t) ∧
      (∀ t,AEStronglyMeasurable[F t] (V t) μ) := by
  let Y := fun t ω => X (min t H) ω
  let D := HeatPathMaximum.value H X
  have hXm : ∀ t,Measurable (X t) := fun t => (ha t).measurable.mono (F.le t) le_rfl
  have hDm : StronglyMeasurable D := (HeatPathMaximum.measurable H X hXm hc).stronglyMeasurable
  have hD : MemLp D 2 μ := (memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).mpr hmax
  have hD0 : ∀ ω,0 ≤ D ω := fun ω => ENNReal.toReal_nonneg
  have hYm : ∀ t,StronglyMeasurable (Y t) := fun t => ((ha (min t H)).mono (F.le (min t H)))
  have hYc : ∀ ω,Continuous (fun t => Y t ω) := fun ω =>
    (hc ω).comp (continuous_id.min continuous_const)
  have hYb : ∀ t ω,‖Y t ω‖ ≤ D ω := fun t ω =>
    HeatPathObservation.norm_le_max H X hc (min_le_right t H) ω
  let V := HeatVersionLp.value μ Y hYm D hD hYb
  have hv (t : ℝ≥0) : V t=ᵐ[μ] Y t := HeatVersionLp.value_ae μ Y hYm D hD hYb t
  refine ⟨V,HeatVersionLp.continuous μ Y hYm D hD hD0 hYb hYc,?_,?_⟩
  · intro t ht
    have he : Y t=X t := by dsimp only [Y];rw [min_eq_left ht]
    rw [←he]
    exact hv t
  · intro t
    have hYa : StronglyMeasurable[F t] (Y t) := (ha (min t H)).mono (F.mono (min_le_left t H))
    exact hYa.aestronglyMeasurable.congr (hv t).symm

end HeatWeakEnergyPathValues
#check @HeatWeakEnergyPathValues.exists_continuous_values
#print axioms HeatWeakEnergyPathValues.exists_continuous_values
