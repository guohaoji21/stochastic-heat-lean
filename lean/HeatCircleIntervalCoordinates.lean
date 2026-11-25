import HeatRealOddSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatCircleIntervalCoordinates
open MeasureTheory AddCircle
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The centered representative of a unit-circle point. -/
def coordinate (x : AddCircle (1 : ℝ)) : ℝ :=
  ((AddCircle.equivIoc (1 : ℝ) (-(1 : ℝ)/2) x) : ℝ)

theorem coordinate_mem (x : AddCircle (1 : ℝ)) : coordinate x ∈ Set.Ioc (-(1 : ℝ)/2) (1/2) := by
  have h := (AddCircle.equivIoc (1 : ℝ) (-(1 : ℝ)/2) x).property
  norm_num at h ⊢
  exact h

theorem coordinate_measurePreserving :
    MeasurePreserving coordinate (haarAddCircle (T := (1 : ℝ)))
      (volume.restrict (Set.Ioc (-(1 : ℝ)/2) (1/2))) := by
  have hv : (volume : Measure (AddCircle (1 : ℝ))) = haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
  have hp := (measurePreserving_subtype_coe (measurableSet_Ioc :
    MeasurableSet (Set.Ioc (-(1 : ℝ)/2) (-(1 : ℝ)/2 + 1)))).comp
      (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := -(1 : ℝ)/2))
  rw [hv] at hp
  have hp' : MeasurePreserving coordinate (haarAddCircle (T := (1 : ℝ)))
      (volume.restrict (Set.Ioc (-(1 : ℝ)/2) (-(1 : ℝ)/2 + 1))) := hp
  simpa only [show (-(1 : ℝ)/2 + 1) = 1/2 by norm_num] using hp'

/-- Candidate spatial folding for the interval of length ten. -/
def position (x : AddCircle (1 : ℝ)) : ℝ := 20 * |coordinate x|

theorem position_measurable : Measurable position := by
  exact measurable_const.mul ((continuous_abs.measurable.comp coordinate_measurePreserving.measurable))

theorem position_mem (x : AddCircle (1 : ℝ)) : position x ∈ Set.Icc 0 10 := by
  have h := coordinate_mem x
  have habs : |coordinate x| ≤ (1 : ℝ)/2 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
  constructor <;> dsimp [position] <;> nlinarith [abs_nonneg (coordinate x)]

end HeatCircleIntervalCoordinates
#check @HeatCircleIntervalCoordinates.coordinate_mem
#print axioms HeatCircleIntervalCoordinates.coordinate_mem
#check @HeatCircleIntervalCoordinates.coordinate_measurePreserving
#print axioms HeatCircleIntervalCoordinates.coordinate_measurePreserving
#check @HeatCircleIntervalCoordinates.position_measurable
#print axioms HeatCircleIntervalCoordinates.position_measurable
#check @HeatCircleIntervalCoordinates.position_mem
#print axioms HeatCircleIntervalCoordinates.position_mem
