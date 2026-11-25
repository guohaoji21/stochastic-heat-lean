import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section
namespace HeatDualityRemainder
open Filter
open scoped Topology
variable {ι : Type*}

theorem sum_bound (s : Finset ι) (δ : ℝ) (E F e : ι → ℝ)
    (hE : ∀ i, 0≤E i) (hF : ∀ i, 0≤F i)
    (he : ∀ i∈s, |e i|≤Real.sqrt δ*(Real.sqrt (E i)*Real.sqrt (F i))) :
    |∑ i∈s,e i|≤Real.sqrt δ*Real.sqrt (∑ i∈s,E i)*Real.sqrt (∑ i∈s,F i) := by
  calc
    _ ≤ ∑ i∈s,|e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i∈s,Real.sqrt δ*(Real.sqrt (E i)*Real.sqrt (F i)) := Finset.sum_le_sum he
    _ = Real.sqrt δ*(∑ i∈s,Real.sqrt (E i)*Real.sqrt (F i)) := (Finset.mul_sum ..).symm
    _ ≤ Real.sqrt δ*(Real.sqrt (∑ i∈s,E i)*Real.sqrt (∑ i∈s,F i)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s hE hF) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem tends_zero (δ e : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (A B : ℝ)
    (he : ∀ n, |e n|≤Real.sqrt (δ n)*Real.sqrt A*Real.sqrt B) :
    Tendsto e atTop (𝓝 0) := by
  have hroot : Tendsto (fun n => Real.sqrt (δ n)*Real.sqrt A*Real.sqrt B) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,Real.sqrt_zero,zero_mul] using ((Real.continuous_sqrt.tendsto 0).comp hδ).mul_const (Real.sqrt A) |>.mul_const (Real.sqrt B)
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using he n) hroot

end HeatDualityRemainder
#check @HeatDualityRemainder.sum_bound
#print HeatDualityRemainder.sum_bound
#print axioms HeatDualityRemainder.sum_bound
#check @HeatDualityRemainder.tends_zero
#print axioms HeatDualityRemainder.tends_zero
