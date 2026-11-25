import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace HeatCovarianceTimeScale
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The time change which turns the stochastic cross bracket into r K(r).
It includes the zero-length case; no stochastic equation is asserted here. -/
theorem covariance_time_change (S : ℝ → E →L[ℝ] E) (M : E →L[ℝ] E) (r : ℝ) (y : E) :
    (∫ u in (0 : ℝ)..r, S (r-u) (M (S u y))) =
      r • ∫ s in (0 : ℝ)..1, S ((1-s)*r) (M (S (s*r) y)) := by
  let f : ℝ → E := fun u => S (r-u) (M (S u y))
  have ht := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) f r
  simp only [mul_zero, mul_one] at ht
  have hfun : (fun s : ℝ => f (r*s)) =
      fun s => S ((1-s)*r) (M (S (s*r) y)) := by
    funext s
    dsimp [f]
    congr 2 <;> ring
  rw [hfun] at ht
  exact ht.symm

end HeatCovarianceTimeScale
#check @HeatCovarianceTimeScale.covariance_time_change
#print axioms HeatCovarianceTimeScale.covariance_time_change
