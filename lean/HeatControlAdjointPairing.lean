import HeatRestrictionAdjoint

set_option autoImplicit false
noncomputable section
namespace HeatControlAdjointPairing
open MeasureTheory HeatRestrictionAdjoint
open scoped NNReal

theorem pairing (U : Lp ℝ 2 paperControlMeasure) (z : Lp ℝ 2 paperDomainMeasure) :
    inner ℝ (paperB U) z=inner ℝ U (paperBstar z) := by
  calc
    _ = inner ℝ z (paperB U) := real_inner_comm _ _
    _ = inner ℝ (paperBstar z) U := (restriction_adjoint_pairing paperDomainMeasure (Set.Ioo (1:ℝ) 2) z U).symm
    _ = _ := real_inner_comm _ _

end HeatControlAdjointPairing
#check @HeatControlAdjointPairing.pairing
#print HeatControlAdjointPairing.pairing
#print axioms HeatControlAdjointPairing.pairing
