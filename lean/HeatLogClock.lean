import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace HeatLogClock
open Filter

theorem log_increment (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    Real.log y-Real.log x≤(y-x)/x := by
  have he := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at he
  convert he using 1 <;> field_simp <;> ring

theorem loglog_step (x y : ℝ) (hx : 1≤x)
    (hrec : 4*(y-x)=Real.log (2*x)) :
    4*(Real.log (Real.log (2*y))-Real.log (Real.log (2*x)))≤x⁻¹ := by
  have hx0 : 0<x := by linarith
  have hlx : 0<Real.log (2*x) := Real.log_pos (by linarith)
  have hxy : x<y := by linarith
  have hy0 : 0<y := hx0.trans hxy
  have hly : 0<Real.log (2*y) := Real.log_pos (by linarith)
  have h1 := log_increment (Real.log (2*x)) (Real.log (2*y)) hlx hly
  have h2 := log_increment (2*x) (2*y) (by positivity) (by positivity)
  have h3 : (Real.log (2*y)-Real.log (2*x))/Real.log (2*x)≤
      ((2*y-2*x)/(2*x))/Real.log (2*x) := div_le_div_of_nonneg_right h2 hlx.le
  have he : 4*(((2*y-2*x)/(2*x))/Real.log (2*x))=x⁻¹ := by
    field_simp
    nlinarith
  linarith

end HeatLogClock
#check @HeatLogClock.log_increment
#print axioms HeatLogClock.log_increment
#check @HeatLogClock.loglog_step
#print axioms HeatLogClock.loglog_step
