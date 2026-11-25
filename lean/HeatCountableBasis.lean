import HeatIntervalNormalization
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatCountableBasis
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E]

theorem orthonormal_set_countable (w : Set E) (hw : Orthonormal ℝ (fun x : w => (x:E))) : w.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof w).countable_of_isDiscrete
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro y hy
  refine ⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩
  ext x
  constructor
  · rintro ⟨hx,hxw⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have hsub : (⟨x,hxw⟩ : w) ≠ ⟨y,hy⟩ := fun h => hne (congrArg Subtype.val h)
    have h0 := hw.inner_eq_zero hsub
    have hxnorm := hw.norm_eq_one (⟨x,hxw⟩ : w)
    have hynorm := hw.norm_eq_one (⟨y,hy⟩ : w)
    have hnorm : ‖x-y‖^2 = 2 := by
      rw [norm_sub_sq_real, hxnorm, hynorm, h0]
      norm_num
    have hd : ‖x-y‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    nlinarith [norm_nonneg (x-y)]
  · intro h
    have he := Set.mem_singleton_iff.mp h
    subst x
    exact ⟨Metric.mem_ball_self (by norm_num), hy⟩

theorem exists_countable_hilbertBasis :
    ∃ (w : Set E), w.Countable ∧ Nonempty (HilbertBasis w ℝ E) := by
  obtain ⟨w,b,hb⟩ := exists_hilbertBasis ℝ E
  refine ⟨w, orthonormal_set_countable w ?_, ⟨b⟩⟩
  rw [← hb]
  exact b.orthonormal

end HeatCountableBasis
#check @HeatCountableBasis.orthonormal_set_countable
#print axioms HeatCountableBasis.orthonormal_set_countable
#check @HeatCountableBasis.exists_countable_hilbertBasis
#print axioms HeatCountableBasis.exists_countable_hilbertBasis
