import HeatWeightedBackwardCell
import HeatBackwardChain

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatBackwardNodes
open MeasureTheory HeatCovarianceOperator
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

include hS hcontr in
theorem left_value {Ω : Type*} [MeasurableSpace Ω] {H a b : ℝ≥0} (hab : a < b) (hbH : b ≤ H)
    (W : ℝ≥0 → Ω → ℝ) (P : Ω → ℝ) (q : E) (ω : Ω) :
    (P ω / ((b:ℝ)-(a:ℝ))) • HeatBackwardCell.state H S M W a b q a ω =
      P ω • covariance S hS hcontr M (b-a) q := by
  rw [HeatBackwardCell.left_state,HeatBackwardDrift.drift_covariance S hS hcontr M hab.le hbH,
    smul_smul,NNReal.coe_sub hab.le]
  congr 1
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (by exact_mod_cast hab)))

theorem right_value {Ω : Type*} [MeasurableSpace Ω] {H a b : ℝ≥0}
    (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (W : ℝ≥0 → Ω → ℝ) (P : Ω → ℝ) (q : E) (ω : Ω) :
    (P ω / ((b:ℝ)-(a:ℝ))) • HeatBackwardCell.state H S M W a b q b ω =
      (P ω*(W b ω-W a ω)/((b:ℝ)-(a:ℝ))) • q := by
  rw [HeatBackwardCell.terminal H S M hzero,smul_smul]
  congr 1
  ring

include hS hcontr in
def cellState {Ω : Type*} [MeasurableSpace Ω] (H : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (g : E)
    (j : ℕ) (s : ℝ≥0) (ω : Ω) : E :=
  (HeatBrownianProducts.products W t (j-1) ω / ((t j:ℝ)-(t (j-1):ℝ))) •
    HeatBackwardCell.state H S M W (t (j-1)) (t j)
      (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j) s ω

include hS hcontr in
theorem node_match {Ω : Type*} [MeasurableSpace Ω] {H : ℝ≥0} (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (g : E)
    {j : ℕ} (hj : 1 ≤ j) (hjN : j < N)
    (hnext : t j < t (j+1)) (hT : t (j+1) ≤ H) (ω : Ω) :
    cellState S hS hcontr M H W t N g j (t j) ω =
      cellState S hS hcontr M H W t N g (j+1) (t j) ω := by
  let K := covariance S hS hcontr M
  let h : ℕ → ℝ≥0 := fun k => t k-t (k-1)
  let q : ℕ → E := HeatBackwardChain.stateAt K h N g
  have hrec := HeatBackwardChain.recurrence K h N g (Nat.succ_pos j) (Nat.succ_le_iff.mpr hjN)
  have hp : HeatBrownianProducts.products W t j ω =
      HeatBrownianProducts.products W t (j-1) ω * (W (t j) ω-W (t (j-1)) ω) /
        ((t j:ℝ)-(t (j-1):ℝ)) := by
    have he : j = (j-1)+1 := by omega
    conv_lhs => rw [he]
    rw [HeatBrownianProducts.products]
    simp only [show j-1+1=j by omega]
  unfold cellState
  rw [right_value S M hzero]
  simp only [Nat.add_sub_cancel]
  rw [left_value S hS hcontr M hnext hT]
  rw [←hp]
  exact congrArg (fun x : E => HeatBrownianProducts.products W t j ω • x) hrec

end HeatBackwardNodes
#check @HeatBackwardNodes.left_value
#print axioms HeatBackwardNodes.left_value
#check @HeatBackwardNodes.right_value
#print axioms HeatBackwardNodes.right_value
#check @HeatBackwardNodes.node_match
#print axioms HeatBackwardNodes.node_match
