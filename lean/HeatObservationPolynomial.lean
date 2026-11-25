import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace HeatObservationPolynomial
open MeasureTheory Set

theorem integral (a b : ℝ) :
    (∫ s in a..b, (s-a)+(b-s)^2)=(b-a)^2/2+(b-a)^3/3 := by
  let p := fun s : ℝ => (s-a)^2/2-(b-s)^3/3
  have hd : ∀ s,HasDerivAt p ((s-a)+(b-s)^2) s := by
    intro s
    have hh := (((hasDerivAt_id s).sub_const a).pow 2).div_const 2
    have hk := (((hasDerivAt_const s b).sub (hasDerivAt_id s)).pow 3).div_const 3
    convert hh.sub hk using 1
    · funext x
      rfl
    · norm_num
      ring
  have hi : IntervalIntegrable (fun s : ℝ => (s-a)+(b-s)^2) volume a b :=
    (by fun_prop : Continuous (fun s : ℝ => (s-a)+(b-s)^2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi]
  dsimp [p]
  ring

theorem normalized (a b : ℝ) (hab : a<b) :
    (∫ s in a..b, ((s-a)+(b-s)^2)/(b-a)^2)=1/2+(b-a)/3 := by
  rw [intervalIntegral.integral_div,integral]
  have hn : b-a≠0 := ne_of_gt (sub_pos.mpr hab)
  field_simp
  <;> ring

end HeatObservationPolynomial
#check @HeatObservationPolynomial.integral
#print axioms HeatObservationPolynomial.integral
#check @HeatObservationPolynomial.normalized
#print axioms HeatObservationPolynomial.normalized
