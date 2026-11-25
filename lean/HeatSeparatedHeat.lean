import HeatDaviesGaffney

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatSeparatedHeat
open MeasureTheory Set Filter HeatIntervalNormalization HeatRestrictionAdjoint
open scoped NNReal

theorem restriction_zero (f : Base)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → f x=0) : paperBstar f=0 := by
  have hs : ∀ᵐ x ∂paperControlMeasure,x∉Ioo (6:ℝ) 7 → f x=0 :=
    hsupp.filter_mono (ae_mono Measure.restrict_le_self)
  apply Lp.ext
  filter_upwards [paperBstar_is_restriction f,hs,ae_restrict_mem measurableSet_Ioo,
    Lp.coeFn_zero ℝ 2 paperControlMeasure] with x hx hsup hxin hz
  rw [hx,hz]
  exact hsup (fun hd => by linarith [hxin.2,hd.1])

theorem bound (s L : ℝ≥0) (hL : 0<(L:ℝ)) (hsL : s≤L) (f : Base)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → f x=0) :
    ‖paperBstar (paperHeat s f)‖ ≤ Real.exp (-4/(L:ℝ))*‖f‖ := by
  by_cases hz : s=0
  · rw [hz]
    simp only [NNReal.coe_zero,paperHeat_zero,ContinuousLinearMap.id_apply,restriction_zero f hsupp,norm_zero]
    positivity
  · have hs : 0<(s:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hz : 0<s)
    have hratio : (4:ℝ)/(L:ℝ)≤4/(s:ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hs (by exact_mod_cast hsL)
    have he : Real.exp (-4/(s:ℝ))≤Real.exp (-4/(L:ℝ)) := Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hratio)
    exact (HeatDaviesGaffney.bound s hs f hsupp).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))

end HeatSeparatedHeat
#check @HeatSeparatedHeat.bound
#print HeatSeparatedHeat.bound
#print axioms HeatSeparatedHeat.bound
