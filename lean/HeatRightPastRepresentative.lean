import HeatCanonicalUsualCross56
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace HeatRightPastRepresentative

open Filter MeasureTheory Set HeatNullAugmentation56
open scoped NNReal Topology

variable {Ω E : Type*} [m₀ : MeasurableSpace Ω] [NormedAddCommGroup E] [CompleteSpace E]

/-- A strongly measurable map for the sigma algebra of almost measurable
sets has an actual representative for the smaller sigma algebra. -/
theorem aeStronglyMeasurable_eventual {μ : Measure Ω} {m : MeasurableSpace Ω} {f : Ω → E}
    (hf : StronglyMeasurable[eventuallyMeasurableSpace m (ae μ)] f) : AEStronglyMeasurable[m] f μ := by
  classical
  let a := ae μ
  have hallseq (q : Ω → ℕ → Prop) : (∀ᵐ ω ∂μ, ∀ n, q ω n) ↔ ∀ n, ∀ᵐ ω ∂μ, q ω n :=
    ae_all_iff
  letI : MeasurableSpace Ω := eventuallyMeasurableSpace m a
  let p := hf.approx
  have hfiber (n : ℕ) (v : E) : ∃ A : Set Ω, MeasurableSet[m] A ∧ p n ⁻¹' {v} =ᶠ[a] A :=
    (p n).measurableSet_fiber v
  choose A hA hsp using hfiber
  let g (n : ℕ) (ω : Ω) : E := ∑ v ∈ (p n).range, (A n v).indicator (fun _ => v) ω
  have hg (n : ℕ) : StronglyMeasurable[m] (g n) :=
    (p n).range.stronglyMeasurable_fun_sum (fun v _ => stronglyMeasurable_const.indicator (hA n v))
  have hgp (n : ℕ) : g n =ᶠ[a] p n := by
    have hall : ∀ᶠ ω in a, ∀ v ∈ (p n).range, (p n ω = v) = (ω ∈ A n v) :=
      (eventually_all_finset _).mpr fun v _ => hsp n v
    filter_upwards [hall] with ω hω
    dsimp only [g]
    rw [Finset.sum_eq_single_of_mem (p n ω) ((p n).mem_range_self ω)]
    · exact indicator_of_mem ((Iff.of_eq (hω _ ((p n).mem_range_self ω))).mp rfl) _
    · intro v hv hne
      exact indicator_of_notMem (fun hvA => hne ((Iff.of_eq (hω v hv)).mpr hvA).symm) _
  refine ⟨fun ω => limUnder atTop (fun n => g n ω), ?_, ?_⟩
  · letI : MeasurableSpace Ω := m
    exact StronglyMeasurable.limUnder hg
  filter_upwards [(hallseq _).mpr hgp] with ω hω
  exact ((hf.tendsto_approx ω).congr (fun n => (hω n).symm)).limUnder_eq.symm

theorem rightCont_le_eventual {μ : Measure Ω} [μ.IsComplete] (F : Filtration ℝ≥0 m₀)
    {s t : ℝ≥0} (hst : s < t) :
    (nullAugmentation (μ := μ) F).rightCont s ≤ eventuallyMeasurableSpace (F t) (ae μ) := by
  have hle : (nullAugmentation (μ := μ) F).rightCont s ≤ nullAugmentation (μ := μ) F t := by
    rw [Filtration.rightCont_eq]
    exact iInf₂_le t hst
  refine hle.trans (sup_le le_eventuallyMeasurableSpace ?_)
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact ⟨∅, @MeasurableSet.empty Ω (F t), by
    have h : ∀ᵐ ω ∂μ, ω ∉ A := ae_iff.mpr (by simpa using hA)
    filter_upwards [h] with ω hω
    simp [hω]⟩

/-- A random variable known at time `s` in the usual augmentation has a
raw measurable representative at each strictly later deterministic time. -/
theorem right_past {μ : Measure Ω} [μ.IsComplete] (F : Filtration ℝ≥0 m₀)
    {s t : ℝ≥0} (hst : s < t) {f : Ω → E}
    (hf : AEStronglyMeasurable[(nullAugmentation (μ := μ) F).rightCont s] f μ) :
    AEStronglyMeasurable[F t] f μ := by
  have hg := hf.stronglyMeasurable_mk.mono (rightCont_le_eventual F hst)
  exact (aeStronglyMeasurable_eventual hg).congr hf.ae_eq_mk.symm

end HeatRightPastRepresentative

#print axioms HeatRightPastRepresentative.right_past
