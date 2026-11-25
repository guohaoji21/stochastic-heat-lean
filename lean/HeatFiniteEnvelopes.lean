import HeatContinuousCells
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatFiniteEnvelopes
open MeasureTheory
open scoped NNReal ENNReal
variable {Ω E : Type*} [NormedAddCommGroup E]

theorem paste_bound (t : ℕ → ℝ≥0) (f : ℕ → ℝ≥0 → Ω → E) (N : ℕ)
    (D : ℕ → Ω → ℝ) (hD : ∀ j, 1 ≤ j → j ≤ N → ∀ ω, 0 ≤ D j ω)
    (hb : ∀ j, 1 ≤ j → j ≤ N → ∀ x, t (j-1) ≤ x → x ≤ t j → ∀ ω, ‖f j x ω‖ ≤ D j ω) :
    ∀ n, n < N → ∀ x, t 0 ≤ x → x ≤ t (n+1) → ∀ ω,
      ‖HeatContinuousCells.paste t (fun j x => f j x ω) n x‖ ≤ ∑ j ∈ Finset.Icc 1 (n+1), D j ω := by
  intro n
  induction n with
  | zero =>
    intro hn x hx0 hxt ω
    simpa only [HeatContinuousCells.paste,Finset.Icc_self,Finset.sum_singleton] using hb 1 (by omega) (by omega) x hx0 hxt ω
  | succ n ih =>
    intro hn x hx0 hxt ω
    by_cases hs : x ≤ t (n+1)
    · simp only [HeatContinuousCells.paste,hs,ite_true]
      have hh := ih (by omega) x hx0 hs ω
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (n+1)+1)]
      exact hh.trans (le_add_of_nonneg_right (hD (n+2) (by omega) (by omega) ω))
    · simp only [HeatContinuousCells.paste,hs,ite_false]
      have hh := hb (n+2) (by omega) (by omega) x (le_of_not_ge hs) hxt ω
      exact hh.trans (Finset.single_le_sum (fun j hj => hD j (Finset.mem_Icc.mp hj).1 ((Finset.mem_Icc.mp hj).2.trans (by omega)) ω)
        (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩))

section L2
variable [MeasurableSpace Ω] (μ : Measure Ω)

theorem sum_memLp (D : ℕ → Ω → ℝ) (N : ℕ) (hD : ∀ j, 1 ≤ j → j ≤ N → MemLp (D j) 2 μ) :
    MemLp (fun ω => ∑ j ∈ Finset.Icc 1 N, D j ω) 2 μ := by
  exact memLp_finsetSum _ (fun j hj => hD j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)

end L2
end HeatFiniteEnvelopes
#check @HeatFiniteEnvelopes.paste_bound
#print axioms HeatFiniteEnvelopes.paste_bound
#check @HeatFiniteEnvelopes.sum_memLp
#print axioms HeatFiniteEnvelopes.sum_memLp
