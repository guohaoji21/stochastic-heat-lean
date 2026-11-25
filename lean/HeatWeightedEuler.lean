import HeatWeightedResolvent
import HeatDirichletEuler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatWeightedEuler
open MeasureTheory Filter HeatIntervalNormalization HeatDirichletResolvent HeatEulerScalar HeatExponentialWeight
open scoped Topology

theorem smoothing_bound {a α : ℝ} (ha : 1≤a) (hα : α^2<a) (f : Base) :
    ‖weight α (smoothing a ha f)‖≤(a/(a-α^2))*‖weight α f‖ := by
  change ‖weight α (a • resolvent a ha f)‖≤_
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤a)]
  calc
    _ ≤ a*(‖weight α f‖/(a-α^2)) := mul_le_mul_of_nonneg_left (HeatWeightedResolvent.bound ha hα f) (by linarith)
    _ = _ := by ring

theorem iterate_bound {a α : ℝ} (ha : 1≤a) (hα : α^2<a) (f : Base) (n : ℕ) :
    ‖weight α (((smoothing a ha : Base → Base)^[n]) f)‖≤(a/(a-α^2))^n*‖weight α f‖ := by
  have hc : 0≤a/(a-α^2) := div_nonneg (by linarith) (sub_pos.mpr hα).le
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ (a/(a-α^2))*‖weight α (((smoothing a ha : Base → Base)^[n]) f)‖ := smoothing_bound ha hα _
      _ ≤ (a/(a-α^2))*((a/(a-α^2))^n*‖weight α f‖) := mul_le_mul_of_nonneg_left ih hc
      _ = _ := by rw [pow_succ];ring

theorem ratio {T : ℝ} (hT : 0<T) (α : ℝ) (n : ℕ) :
    parameter T n/(parameter T n-α^2)=(1+(T*(-α^2))/(count T n:ℝ))⁻¹ := by
  have hk : (0:ℝ)<count T n := by exact_mod_cast count_positive T n
  have ha : parameter T n≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (parameter_ge_one hT n))
  have he : 1+(T*(-α^2))/(count T n:ℝ)=(parameter T n-α^2)/(parameter T n) := by
    unfold parameter
    field_simp
    ring
  rw [he,inv_div]

theorem coefficient_tendsto {T : ℝ} (hT : 0<T) (α : ℝ) :
    Tendsto (fun n => (parameter T n/(parameter T n-α^2))^(count T n)) atTop (𝓝 (Real.exp (T*α^2))) := by
  simp_rw [ratio hT α]
  have h := (tendsto_inverse (T*(-α^2))).comp (count_tendsto T)
  convert h using 1
  congr 1
  ring

theorem heat_bound (T : ℝ) (hT : 0≤T) (α : ℝ) (f : Base) :
    ‖weight α (paperHeat T f)‖≤Real.exp (T*α^2)*‖weight α f‖ := by
  rcases eq_or_lt_of_le hT with hz | hp
  · subst T
    simp only [paperHeat_zero,ContinuousLinearMap.id_apply,zero_mul,Real.exp_zero,one_mul,le_rfl]
  · have hk : Tendsto (fun n => (count T n:ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (count_tendsto T)
    have hev : ∀ᶠ n in atTop,α^2<parameter T n := by
      filter_upwards [hk.eventually_gt_atTop (T*α^2)] with n hn
      exact (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using hn)
    have hL := (((weight α).continuous.tendsto (paperHeat T f)).comp (HeatDirichletEuler.tendsto_heat T hp f)).norm
    have hR := (coefficient_tendsto hp α).mul_const ‖weight α f‖
    apply le_of_tendsto_of_tendsto hL hR
    filter_upwards [hev] with n hn
    exact iterate_bound (parameter_ge_one hp n) hn f (count T n)

end HeatWeightedEuler
#check @HeatWeightedEuler.heat_bound
#print HeatWeightedEuler.heat_bound
#print axioms HeatWeightedEuler.heat_bound
