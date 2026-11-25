import SHEStochastic.ContinuousNormExit
import SHE.NullCompleteFiltration
import SHE.ContinuousPredictable

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatContinuousLocalization
open MeasureTheory Filter Set
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem exists_version (hn : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (G : ℝ≥0 → Ω → E) (hGc : ∀ ω, Continuous (fun t => G t ω))
    (D : Ω → ℝ) (hD : ∀ t ω, t≤H → ‖G t ω‖≤D ω)
    (V : ℝ≥0 → Lp E 2 μ)
    (hVa : ∀ t, ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ V t=ᵐ[μ] Z)
    (Y : ℕ → ℝ≥0 → Ω → E) (hYc : ∀ n ω, Continuous (fun t => Y n t ω))
    (hY : ∀ n t, t≤H → ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0)<SHEStochastic.ContinuousNormExit.exit G n ω →
      Y n t ω=V t ω) :
    ∃ Z : ℝ≥0 → Ω → E, (∀ ω, Continuous (fun t => Z t ω)) ∧ StronglyAdapted F Z ∧
      StronglyMeasurable[F.predictable] (Function.uncurry Z) ∧
      ∀ t, t≤H → Z t=ᵐ[μ] V t := by
  have hchoose (ω : Ω) : ∃ n : ℕ, D ω<n := exists_nat_gt (D ω)
  let N : Ω → ℕ := fun ω => Classical.choose (hchoose ω)
  have hN (ω : Ω) : D ω<N ω := Classical.choose_spec (hchoose ω)
  have hτ (ω : Ω) : (H : WithTop ℝ≥0)<SHEStochastic.ContinuousNormExit.exit G (N ω) ω := by
    by_contra hn
    obtain ⟨s,hs,hnorm⟩ := (SHEStochastic.ContinuousNormExit.le_iff G hGc (N ω) H ω).mp (le_of_not_gt hn)
    exact (not_le_of_gt (hN ω)) (hnorm.trans (hD s ω hs.2))
  let Z : ℝ≥0 → Ω → E := fun t ω => Y (N ω) (min t H) ω
  have hZc (ω : Ω) : Continuous (fun t => Z t ω) :=
    (hYc (N ω) ω).comp (continuous_id.min continuous_const)
  have hrep (t : ℝ≥0) (ht : t≤H) : Z t=ᵐ[μ] V t := by
    filter_upwards [ae_all_iff.mpr (fun n => hY n t ht)] with ω hω
    change Y (N ω) (min t H) ω=V t ω
    rw [min_eq_left ht]
    exact hω (N ω) (lt_of_le_of_lt (by exact_mod_cast ht) (hτ ω))
  have hZa : StronglyAdapted F Z := by
    intro t
    by_cases ht : t≤H
    · obtain ⟨W,hW,he⟩ := hVa t
      exact SHE.NullCompleteFiltration.stronglyMeasurable_congr F μ hn t hW ((hrep t ht).trans he)
    · have hHt : H≤t := le_of_not_ge ht
      have hZH : StronglyMeasurable[F H] (Z H) := by
        obtain ⟨W,hW,he⟩ := hVa H
        exact SHE.NullCompleteFiltration.stronglyMeasurable_congr F μ hn H hW ((hrep H le_rfl).trans he)
      have heq : Z t=Z H := by funext ω;simp only [Z,min_eq_right hHt,min_self]
      rw [heq]
      exact hZH.mono (F.mono hHt)
  exact ⟨Z,hZc,hZa,SHE.ContinuousPredictable.stronglyMeasurable F Z hZa hZc,hrep⟩

end HeatContinuousLocalization
#check @HeatContinuousLocalization.exists_version
#print HeatContinuousLocalization.exists_version
#print axioms HeatContinuousLocalization.exists_version
