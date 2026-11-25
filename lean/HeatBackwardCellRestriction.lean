import HeatBackwardNoise
import HeatBackwardKernel

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatBackwardCellRestriction
open MeasureTheory Set SHE SHE.PredictableL2 HeatCovarianceOperator
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

theorem raw_cell (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (N : ℕ) (g : E) (j : ℕ) (hj : j ∈ Finset.Icc 1 N)
    (s : ℝ≥0) (hs : s ∈ Ioc (t (j-1)) (t j)) (ω : Ω) :
    HeatBackwardNoise.raw S hS hcontr M W t N g (s,ω) =
      HeatBackwardNoise.coefficient W t j ω • S (t j-s)
        (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j) := by
  classical
  unfold HeatBackwardNoise.raw
  rw [Finset.sum_eq_single (⟨j,hj⟩ : {j // j ∈ Finset.Icc 1 N})]
  · simp [PredictableSteps.step,hs]
  · intro i hi hij
    have hne : (i:ℕ) ≠ j := fun he => hij (Subtype.ext he)
    have hn : ¬ (t (i-1) < s ∧ s ≤ t i) := by
      intro hh
      rcases lt_or_gt_of_ne hne with hl | hr
      · have htij : t i ≤ t (j-1) := ht (by omega)
        exact (not_lt_of_ge (hh.2.trans htij)) hs.1
      · have htji : t j ≤ t (i-1) := ht (by omega)
        exact (not_lt_of_ge (hs.2.trans htji)) hh.1
    simp [PredictableSteps.step,hn]
  · simp

theorem state_cell {H : ℝ≥0} (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (N : ℕ) (hN : 1 ≤ N) (g : E) (j : ℕ) (hj : j ∈ Finset.Icc 1 N)
    (s : ℝ≥0) (hs : s ∈ Ioc (t (j-1)) (t j)) (ω : Ω) :
    HeatBackwardProcess.state S hS hcontr M H W t N g s ω =
      HeatBackwardNodes.cellState S hS hcontr M H W t N g j s ω := by
  exact HeatContinuousCells.cell_value t ht _ (N-1) j
    (Finset.mem_Icc.mp hj).1 (by simpa only [Nat.sub_add_cancel hN] using (Finset.mem_Icc.mp hj).2)
    s hs.1 hs.2

end HeatBackwardCellRestriction
#check @HeatBackwardCellRestriction.raw_cell
#print axioms HeatBackwardCellRestriction.raw_cell
#check @HeatBackwardCellRestriction.state_cell
#print axioms HeatBackwardCellRestriction.state_cell
