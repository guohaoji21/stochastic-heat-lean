import HeatCovarianceSeparation
import HeatBackwardChain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatChainSeparation
open MeasureTheory Set HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

variable (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
  (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖≤1)
  (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → b x=0)

include hsupp in
theorem heat_state_bound (h : ℕ → ℝ≥0) (N : ℕ) (g : Base)
    (hgsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → g x=0)
    (j : ℕ) (hj : j≤N) (r : ℝ≥0) (hr : r≤h j) (hpos : 0<(h j:ℝ)) (hnext : h (j+1)≤h j) :
    ‖paperBstar (family r (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g j))‖≤
      Real.exp (-4/(2*(h j:ℝ)))*‖g‖ := by
  let L := 2*h j
  have hL : 0<(L:ℝ) := by dsimp [L];positivity
  by_cases hjN : j=N
  · subst j
    rw [HeatBackwardChain.terminal]
    have hrL : r≤L := hr.trans (by dsimp [L];simpa only [two_mul] using (le_add_of_nonneg_right (show (0:ℝ≥0)≤h N from bot_le) : h N≤h N+h N))
    have he := HeatSeparatedHeat.bound r L hL hrL g hgsupp
    simpa only [L,NNReal.coe_mul,NNReal.coe_ofNat,family] using he
  · have hjlt : j<N := lt_of_le_of_ne hj hjN
    have heq := HeatBackwardChain.recurrence (HeatPaperCovariance.K b hb hbound) h N g
      (j := j+1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at heq
    rw [heq]
    have hsum : r+h (j+1)≤L := by
      calc
        _ ≤ h j+h j := add_le_add hr hnext
        _ = L := by dsimp [L];ring
    have he := HeatCovarianceSeparation.heat_covariance_bound b hb hbound hsupp r (h (j+1)) L hL hsum
      (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g (j+1))
    have hnorm := HeatBackwardChain.norm_bound (HeatPaperCovariance.K b hb hbound)
      (HeatPaperCovariance.K_contraction b hb hbound) h N g (j+1)
    have hfinal := he.trans (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)
    simpa only [L,NNReal.coe_mul,NNReal.coe_ofNat] using hfinal

include hsupp in
theorem covariance_state_bound (h : ℕ → ℝ≥0) (N : ℕ) (g : Base)
    (j : ℕ) (r : ℝ≥0) (hr : r≤h j) (hpos : 0<(h j:ℝ)) :
    ‖paperBstar (HeatPaperCovariance.K b hb hbound r
      (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g j))‖≤
      Real.exp (-4/(2*(h j:ℝ)))*‖g‖ := by
  let L := 2*h j
  have hL : 0<(L:ℝ) := by dsimp [L];positivity
  have hrL : r≤L := hr.trans (by dsimp [L];simpa only [two_mul] using (le_add_of_nonneg_right (show (0:ℝ≥0)≤h j from bot_le) : h j≤h j+h j))
  have he := HeatCovarianceSeparation.covariance_bound b hb hbound hsupp r L hL hrL
    (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g j)
  have hnorm := HeatBackwardChain.norm_bound (HeatPaperCovariance.K b hb hbound)
    (HeatPaperCovariance.K_contraction b hb hbound) h N g j
  have hfinal := he.trans (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)
  simpa only [L,NNReal.coe_mul,NNReal.coe_ofNat] using hfinal

end HeatChainSeparation
#check @HeatChainSeparation.heat_state_bound
#print HeatChainSeparation.heat_state_bound
#print axioms HeatChainSeparation.heat_state_bound
#check @HeatChainSeparation.covariance_state_bound
#print axioms HeatChainSeparation.covariance_state_bound
