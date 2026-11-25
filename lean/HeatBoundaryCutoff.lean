import HeatWeakSecondDerivative
import EllipticPdes.Sobolev.GraphLattice
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatBoundaryCutoff
open MeasureTheory Filter Set
open scoped Topology


theorem step_derivative_zero_left (x : ℝ) (hx : x ≤ 0) : deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply IsMinOn.isLocalMin (s := Set.univ)
  · intro y _
    change Real.smoothTransition x ≤ Real.smoothTransition y
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  · exact Filter.univ_mem

theorem step_derivative_zero_right (x : ℝ) (hx : 1 ≤ x) : deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply IsMaxOn.isLocalMax (s := Set.univ)
  · intro y _
    change Real.smoothTransition y ≤ Real.smoothTransition x
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y
  · exact Filter.univ_mem

theorem step_derivative_support : tsupport (deriv Real.smoothTransition) ⊆ Set.Icc (0 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  change deriv Real.smoothTransition x ≠ 0 at hx
  constructor
  · by_contra hn
    exact hx (step_derivative_zero_left x (le_of_not_ge hn))
  · by_contra hn
    exact hx (step_derivative_zero_right x (le_of_not_ge hn))

theorem step_derivative_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) := (@Real.smoothTransition.contDiff (2 : ℕ∞)).continuous_deriv (by norm_num)
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have hn : |deriv Real.smoothTransition x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
    exact hn.trans (le_max_left _ _)
  · have hz : deriv Real.smoothTransition x = 0 := by
      by_contra hn
      exact hx (step_derivative_support (subset_closure hn))
    rw [hz, abs_zero]
    exact le_max_right _ _

def cutoff (a x : ℝ) : ℝ := Real.smoothTransition (x/a-1) * Real.smoothTransition ((10-x)/a-1)

theorem cutoff_smooth (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoff a) := by
  unfold cutoff
  fun_prop

theorem cutoff_bounds (a x : ℝ) : 0 ≤ cutoff a x ∧ cutoff a x ≤ 1 := by
  unfold cutoff
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩

theorem cutoff_zero_left (a x : ℝ) (ha : 0 < a) (hx : x ≤ a) : cutoff a x = 0 := by
  unfold cutoff
  have hz : x/a-1 ≤ 0 := by apply sub_nonpos.mpr; exact (div_le_one ha).mpr hx
  rw [Real.smoothTransition.zero_of_nonpos hz, zero_mul]

theorem cutoff_zero_right (a x : ℝ) (ha : 0 < a) (hx : 10-a ≤ x) : cutoff a x = 0 := by
  unfold cutoff
  have hz : (10-x)/a-1 ≤ 0 := by apply sub_nonpos.mpr; apply (div_le_one ha).mpr; linarith
  rw [Real.smoothTransition.zero_of_nonpos hz, mul_zero]

theorem cutoff_one (a x : ℝ) (ha : 0 < a) (hx : 2*a ≤ x) (hx' : x ≤ 10-2*a) : cutoff a x = 1 := by
  unfold cutoff
  have h1 : 1 ≤ x/a-1 := by have := (le_div_iff₀ ha).mpr hx; linarith
  have h2 : 1 ≤ (10-x)/a-1 := by have := (le_div_iff₀ ha).mpr (show 2*a ≤ 10-x by linarith); linarith
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

theorem cutoff_support (a : ℝ) (ha : 0 < a) : tsupport (cutoff a) ⊆ Set.Icc a (10-a) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  change cutoff a x ≠ 0 at hx
  constructor
  · by_contra hn
    exact hx (cutoff_zero_left a x ha (le_of_not_ge hn))
  · by_contra hn
    exact hx (cutoff_zero_right a x ha (le_of_not_ge hn))

end HeatBoundaryCutoff
#check @HeatBoundaryCutoff.step_derivative_zero_left
#print axioms HeatBoundaryCutoff.step_derivative_zero_left
#check @HeatBoundaryCutoff.step_derivative_zero_right
#print axioms HeatBoundaryCutoff.step_derivative_zero_right
#check @HeatBoundaryCutoff.step_derivative_support
#print axioms HeatBoundaryCutoff.step_derivative_support
#check @HeatBoundaryCutoff.step_derivative_bounded
#print axioms HeatBoundaryCutoff.step_derivative_bounded
#check @HeatBoundaryCutoff.cutoff_smooth
#print axioms HeatBoundaryCutoff.cutoff_smooth
#check @HeatBoundaryCutoff.cutoff_bounds
#print axioms HeatBoundaryCutoff.cutoff_bounds
#check @HeatBoundaryCutoff.cutoff_zero_left
#print axioms HeatBoundaryCutoff.cutoff_zero_left
#check @HeatBoundaryCutoff.cutoff_zero_right
#print axioms HeatBoundaryCutoff.cutoff_zero_right
#check @HeatBoundaryCutoff.cutoff_one
#print axioms HeatBoundaryCutoff.cutoff_one
#check @HeatBoundaryCutoff.cutoff_support
#print axioms HeatBoundaryCutoff.cutoff_support
