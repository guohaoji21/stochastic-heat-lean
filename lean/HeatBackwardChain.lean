import HeatWeightedBackwardCell
import HeatBrownianProducts

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatBackwardChain
open MeasureTheory HeatCovarianceOperator
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def reverseChain (K : ℝ≥0 → E →L[ℝ] E) (h : ℕ → ℝ≥0) (N : ℕ) (g : E) : ℕ → E
  | 0 => g
  | n+1 => K (h (N-n)) (reverseChain K h N g n)

def stateAt (K : ℝ≥0 → E →L[ℝ] E) (h : ℕ → ℝ≥0) (N : ℕ) (g : E) (j : ℕ) : E :=
  reverseChain K h N g (N-j)

theorem terminal (K : ℝ≥0 → E →L[ℝ] E) (h : ℕ → ℝ≥0) (N : ℕ) (g : E) : stateAt K h N g N = g := by
  simp only [stateAt,Nat.sub_self,reverseChain]

theorem recurrence (K : ℝ≥0 → E →L[ℝ] E) (h : ℕ → ℝ≥0) (N : ℕ) (g : E)
    {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    stateAt K h N g (j-1) = K (h j) (stateAt K h N g j) := by
  have hi : N-(j-1) = (N-j)+1 := by omega
  have hk : N-(N-j) = j := by omega
  simp only [stateAt,hi,reverseChain,hk]

theorem norm_bound (K : ℝ≥0 → E →L[ℝ] E) (hK : ∀ r x, ‖K r x‖ ≤ ‖x‖)
    (h : ℕ → ℝ≥0) (N : ℕ) (g : E) (j : ℕ) : ‖stateAt K h N g j‖ ≤ ‖g‖ := by
  have hb : ∀ n, ‖reverseChain K h N g n‖ ≤ ‖g‖ := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (hK _ _).trans ih
  exact hb (N-j)

end HeatBackwardChain
#check @HeatBackwardChain.terminal
#print axioms HeatBackwardChain.terminal
#check @HeatBackwardChain.recurrence
#print axioms HeatBackwardChain.recurrence
#check @HeatBackwardChain.norm_bound
#print axioms HeatBackwardChain.norm_bound
