import HeatSubeigenEuler

set_option autoImplicit false
noncomputable section
namespace HeatL2Order
open MeasureTheory HeatIntervalNormalization

theorem inner_mono (q f g : Base) (hq : ∀ᵐ x ∂baseMeasure,0≤q x)
    (hfg : ∀ᵐ x ∂baseMeasure,f x≤g x) : inner ℝ q f≤ inner ℝ q g := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner q f) (L2.integrable_inner q g)
  filter_upwards [hq,hfg] with x hx hy
  simp only [Real.inner_apply]
  exact mul_le_mul_of_nonneg_left hy hx

theorem inner_positive (f g : Base) (hf : ∀ᵐ x ∂baseMeasure,0≤f x)
    (hfg : ∀ᵐ x ∂baseMeasure,f x≤g x) (hne : f≠0) : 0 < inner ℝ g f := by
  have h := inner_mono f f g hf hfg
  rw [real_inner_self_eq_norm_sq,real_inner_comm g f] at h
  exact (sq_pos_of_pos (norm_pos_iff.mpr hne)).trans_le h

end HeatL2Order
#check @HeatL2Order.inner_mono
#print axioms HeatL2Order.inner_mono
#check @HeatL2Order.inner_positive
#print HeatL2Order.inner_positive
#print axioms HeatL2Order.inner_positive
