import HeatIntervalNormalization

set_option autoImplicit false
noncomputable section
namespace HeatBaseNontrivial
open MeasureTheory HeatIntervalNormalization
open scoped ENNReal
local instance : IsFiniteMeasure baseMeasure := by unfold baseMeasure;infer_instance

theorem nontrivial : Nontrivial Base := by
  let f : Base := Lp.const 2 baseMeasure (1:ℝ)
  apply nontrivial_of_ne f 0
  intro he
  have hfalse : ∀ᵐ x ∂baseMeasure, False := by
    filter_upwards [Lp.coeFn_const 2 baseMeasure (1:ℝ),Lp.coeFn_zero ℝ 2 baseMeasure] with x hc hz
    change f x=1 at hc
    rw [he] at hc
    rw [hz] at hc
    norm_num at hc
  have hm : baseMeasure=0 := ae_eq_bot.mp (Filter.empty_mem_iff_bot.mp hfalse)
  have hz : baseMeasure Set.univ=0 := by rw [hm];rfl
  simpa [baseMeasure,Real.volume_Ioo] using hz

end HeatBaseNontrivial
#check @HeatBaseNontrivial.nontrivial
#print axioms HeatBaseNontrivial.nontrivial
