import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace HeatContinuousCells
open scoped NNReal
variable {E : Type*} [TopologicalSpace E]

def paste (t : ℕ → ℝ≥0) (f : ℕ → ℝ≥0 → E) : ℕ → ℝ≥0 → E
  | 0 => f 1
  | n+1 => fun x => if x ≤ t (n+1) then paste t f n x else f (n+2) x

theorem tail_value (t : ℕ → ℝ≥0) (f : ℕ → ℝ≥0 → E) (n : ℕ) (x : ℝ≥0)
    (hx : t n < x) : paste t f n x = f (n+1) x := by
  cases n with
  | zero => rfl
  | succ n => simp only [paste,not_le.mpr hx,ite_false]

theorem continuous_prefix (t : ℕ → ℝ≥0) (f : ℕ → ℝ≥0 → E) (N : ℕ)
    (ht : ∀ n, n < N → t n < t (n+1))
    (hf : ∀ j, 1 ≤ j → j ≤ N → Continuous (f j))
    (hm : ∀ j, 1 ≤ j → j < N → f j (t j) = f (j+1) (t j)) :
    ∀ n, n < N → Continuous (paste t f n) := by
  intro n
  induction n with
  | zero => intro hn; exact hf 1 (by omega) (by omega)
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hnew := hf (n+2) (by omega) (by omega)
    apply hprev.if_le hnew continuous_id continuous_const
    intro x hx
    change x = t (n+1) at hx
    subst x
    exact (tail_value t f n (t (n+1)) (ht n (by omega))).trans (hm (n+1) (by omega) hn)

theorem cell_value (t : ℕ → ℝ≥0) (ht : Monotone t) (f : ℕ → ℝ≥0 → E) :
    ∀ n j, 1 ≤ j → j ≤ n+1 → ∀ x, t (j-1) < x → x ≤ t j → paste t f n x = f j x := by
  intro n
  induction n with
  | zero =>
    intro j hj hjn x hlo hhi
    have he : j=1 := by omega
    subst j
    rfl
  | succ n ih =>
    intro j hj hjn x hlo hhi
    by_cases he : j = n+2
    · subst j
      exact tail_value t f (n+1) x hlo
    · have hj' : j ≤ n+1 := by omega
      have hxt : x ≤ t (n+1) := hhi.trans (ht hj')
      simp only [paste,hxt,ite_true]
      exact ih j hj hj' x hlo hhi

theorem initial_value (t : ℕ → ℝ≥0) (ht : Monotone t) (f : ℕ → ℝ≥0 → E) (n : ℕ) :
    paste t f n (t 0) = f 1 (t 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [paste,ht (Nat.zero_le (n+1)),ite_true,ih]

end HeatContinuousCells
#check @HeatContinuousCells.tail_value
#print axioms HeatContinuousCells.tail_value
#check @HeatContinuousCells.continuous_prefix
#print axioms HeatContinuousCells.continuous_prefix
#check @HeatContinuousCells.cell_value
#print axioms HeatContinuousCells.cell_value
#check @HeatContinuousCells.initial_value
#print axioms HeatContinuousCells.initial_value
