import HeatWeightedEuler
import HeatObservationWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatDaviesGaffney
open MeasureTheory Filter Set HeatIntervalNormalization HeatExponentialWeight HeatRestrictionAdjoint

theorem exponential_bound (t : ℝ) (ht : 0≤t) (α : ℝ) (hα : 0≤α) (f : Base)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → f x=0) :
    ‖paperBstar (paperHeat t f)‖ ≤ Real.exp (t*α^2-4*α)*‖f‖ := by
  have h1 := HeatObservationWeight.observation_bound α hα (paperHeat t f)
  have h2 := HeatWeightedEuler.heat_bound t ht (-α) f
  have h3 := HeatObservationWeight.input_bound α hα f hsupp
  calc
    _ ≤ Real.exp (2*α)*‖weight (-α) (paperHeat t f)‖ := h1
    _ ≤ Real.exp (2*α)*(Real.exp (t*(-α)^2)*‖weight (-α) f‖) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ Real.exp (2*α)*(Real.exp (t*(-α)^2)*(Real.exp (-6*α)*‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by
      rw [←mul_assoc,←mul_assoc,←Real.exp_add,←Real.exp_add]
      congr 2
      ring

theorem bound (t : ℝ) (ht : 0<t) (f : Base)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → f x=0) :
    ‖paperBstar (paperHeat t f)‖ ≤ Real.exp (-4/t)*‖f‖ := by
  have h := exponential_bound t ht.le (2/t) (by positivity) f hsupp
  convert h using 1
  congr 2
  field_simp
  ring

end HeatDaviesGaffney
#check @HeatDaviesGaffney.bound
#print HeatDaviesGaffney.bound
#print axioms HeatDaviesGaffney.bound
