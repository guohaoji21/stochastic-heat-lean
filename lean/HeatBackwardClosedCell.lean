import HeatBackwardCellRestriction

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatBackwardClosedCell
open MeasureTheory Set HeatCovarianceOperator
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

include hS hcontr in
theorem cell_value {H : ℝ≥0} (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hN : 1 ≤ N)
    (hstep : ∀ n, n < N → t n < t (n+1)) (hT : t N ≤ H)
    (g : E) (j : ℕ) (hj : j ∈ Finset.Icc 1 N) (a : ℝ≥0)
    (ha : a ∈ Icc (t (j-1)) (t j)) (ω : Ω) :
    HeatBackwardProcess.state S hS hcontr M H W t N g a ω =
      HeatBackwardNodes.cellState S hS hcontr M H W t N g j a ω := by
  by_cases hlo : t (j-1) < a
  · exact HeatBackwardCellRestriction.state_cell S hS hcontr M W t ht N hN g j hj a ⟨hlo,ha.2⟩ ω
  · have he : a=t (j-1) := le_antisymm (le_of_not_gt hlo) ha.1
    subst a
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hjN := (Finset.mem_Icc.mp hj).2
    by_cases hjone : j=1
    · subst j
      unfold HeatBackwardProcess.state
      simp only [Nat.sub_self]
      exact HeatContinuousCells.initial_value t ht _ (N-1)
    · have hi : 1 ≤ j-1 := by omega
      have hprev : j-1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hi,by omega⟩
      have hidx : j-1+1=j := by omega
      have hlt : t (j-1-1) < t (j-1) := by
        have hh := hstep (j-1-1) (by omega)
        simpa only [show j-1-1+1=j-1 by omega] using hh
      rw [HeatBackwardCellRestriction.state_cell S hS hcontr M W t ht N hN g (j-1) hprev
        (t (j-1)) ⟨hlt,le_rfl⟩ ω]
      simpa only [hidx] using HeatBackwardNodes.node_match S hS hcontr M hzero W t N g hi
        (by omega : j-1<N) (by simpa only [hidx] using hstep (j-1) (by omega))
        (by simpa only [hidx] using (ht hjN).trans hT) ω

end HeatBackwardClosedCell
#check @HeatBackwardClosedCell.cell_value
#print axioms HeatBackwardClosedCell.cell_value
