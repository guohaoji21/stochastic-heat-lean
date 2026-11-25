import HeatExponentialWeight
import HeatRestrictionAdjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatObservationWeight
open MeasureTheory Filter Set HeatIntervalNormalization HeatExponentialWeight HeatRestrictionAdjoint

theorem restriction_bound (f : Base) : ‖paperBstar f‖ ≤ ‖f‖ :=
  norm_Lp_toLp_restrict_le (Ioo (1:ℝ) 2) f

theorem observation_bound (α : ℝ) (hα : 0≤α) (f : Base) :
    ‖paperBstar f‖ ≤ Real.exp (2*α)*‖weight (-α) f‖ := by
  have hw : (weight (-α) f : ℝ → ℝ)=ᵐ[paperControlMeasure] fun x => value (-α) x*f x :=
    (weight_ae (-α) f).filter_mono (ae_mono Measure.restrict_le_self)
  have hpoint : ∀ᵐ x ∂paperControlMeasure,‖paperBstar f x‖ ≤ Real.exp (2*α)*‖paperBstar (weight (-α) f) x‖ := by
    filter_upwards [paperBstar_is_restriction f,paperBstar_is_restriction (weight (-α) f),hw,
      ae_restrict_mem measurableSet_Ioo] with x hf hg hx hxin
    have he : 1≤Real.exp (2*α)*value (-α) x := by
      rw [value,←Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by nlinarith [hxin.2])
    rw [hf,hg,hx,norm_mul]
    have hn : ‖value (-α) x‖=value (-α) x := abs_of_pos (Real.exp_pos _)
    rw [hn]
    nlinarith [norm_nonneg (f x)]
  calc
    _ ≤ Real.exp (2*α)*‖paperBstar (weight (-α) f)‖ := Lp.norm_le_mul_norm_of_ae_le_mul hpoint
    _ ≤ _ := mul_le_mul_of_nonneg_left (restriction_bound _) (Real.exp_pos _).le

theorem input_bound (α : ℝ) (hα : 0≤α) (f : Base)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → f x=0) :
    ‖weight (-α) f‖ ≤ Real.exp (-6*α)*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weight_ae (-α) f,hsupp] with x hw hs
  rw [hw,norm_mul]
  have hn : ‖value (-α) x‖=value (-α) x := abs_of_pos (Real.exp_pos _)
  rw [hn]
  by_cases hx : f x=0
  · simp [hx]
  · have hin : x∈Ioo (6:ℝ) 7 := by by_contra h;exact hx (hs h)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (by nlinarith [hin.1])

end HeatObservationWeight
#check @HeatObservationWeight.observation_bound
#print axioms HeatObservationWeight.observation_bound
#check @HeatObservationWeight.input_bound
#print HeatObservationWeight.input_bound
#print axioms HeatObservationWeight.input_bound
