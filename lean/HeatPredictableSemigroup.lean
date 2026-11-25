import SHE.ContinuousPredictable

set_option autoImplicit false
noncomputable section
namespace HeatPredictableSemigroup
open MeasureTheory Filter
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_action (S : ℝ≥0 → E →L[ℝ] E)
    (hS : ∀ x, Continuous (fun t => S t x))
    (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) :
    Continuous (fun p : ℝ≥0 × E => S p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hu : Continuous (fun p : ℝ≥0 × E => dist p.2 p₀.2 +
      dist (S p.1 p₀.2) (S p₀.1 p₀.2)) :=
    (continuous_snd.dist continuous_const).add
      (((hS p₀.2).comp continuous_fst).dist continuous_const)
  have hl : Tendsto (fun p : ℝ≥0 × E => dist p.2 p₀.2 +
      dist (S p.1 p₀.2) (S p₀.1 p₀.2)) (𝓝 p₀) (𝓝 0) := by
    simpa only [dist_self, zero_add] using hu.tendsto p₀
  apply squeeze_zero (fun p => dist_nonneg) _ hl
  intro p
  calc
    _ ≤ dist (S p.1 p.2) (S p.1 p₀.2) + dist (S p.1 p₀.2) (S p₀.1 p₀.2) :=
      dist_triangle _ _ _
    _ ≤ _ := by
      apply add_le_add_left
      simpa only [dist_eq_norm, ← map_sub] using hcontr p.1 (p.2 - p₀.2)

theorem predictable_heat_factor {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
    (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
    (r : ℝ≥0 → ℝ≥0) (hr : Continuous r) (Y : ℝ≥0 → Ω → E)
    (ha : StronglyAdapted F Y) (hc : ∀ ω, Continuous (fun t => Y t ω)) :
    IsStronglyPredictable F (fun t ω => S (r t) (M (Y t ω))) := by
  apply SHE.ContinuousPredictable.isStronglyPredictable F
  · intro t
    exact (S (r t)).continuous.comp_stronglyMeasurable (M.continuous.comp_stronglyMeasurable (ha t))
  · intro ω
    exact (continuous_action S hS hcontr).comp (hr.prodMk (M.continuous.comp (hc ω)))

end HeatPredictableSemigroup
#check @HeatPredictableSemigroup.continuous_action
#print axioms HeatPredictableSemigroup.continuous_action
#check @HeatPredictableSemigroup.predictable_heat_factor
#print axioms HeatPredictableSemigroup.predictable_heat_factor

namespace HeatPredictableSemigroup
open scoped NNReal

theorem continuous_remaining (T : ℝ≥0) : Continuous (fun t : ℝ≥0 => T - t) := by
  fun_prop

end HeatPredictableSemigroup
#check @HeatPredictableSemigroup.continuous_remaining
#print axioms HeatPredictableSemigroup.continuous_remaining

namespace HeatPredictableSemigroup
open MeasureTheory
open scoped NNReal

theorem predictable_heat_integrand {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
    (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Y)
    (hc : ∀ ω, Continuous (fun t => Y t ω)) :
    IsStronglyPredictable F (fun t ω => S (T - t) (M (Y t ω))) :=
  predictable_heat_factor F S hS hcontr M (fun t => T - t) (continuous_remaining T) Y ha hc

end HeatPredictableSemigroup
#check @HeatPredictableSemigroup.predictable_heat_integrand
#print axioms HeatPredictableSemigroup.predictable_heat_integrand
