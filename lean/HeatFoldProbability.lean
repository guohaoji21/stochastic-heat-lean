import HeatCircleIntervalCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace HeatFoldProbability
open MeasureTheory AddCircle HeatCircleIntervalCoordinates
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem cdf_inside (a : ℝ) (ha : 0 ≤ a) (ha10 : a < 10) :
    haarAddCircle {x : AddCircle (1 : ℝ) | position x ≤ a} = ENNReal.ofReal (a / 10) := by
  have hset : {x : AddCircle (1 : ℝ) | position x ≤ a} =
      coordinate ⁻¹' Set.Icc (-a/20) (a/20) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, position]
    constructor
    · intro h
      have h' : |coordinate x| ≤ a/20 := by linarith
      simpa only [neg_div] using (abs_le.mp h')
    · intro h
      have h' : |coordinate x| ≤ a/20 := abs_le.mpr (by simpa only [neg_div] using h)
      linarith
  rw [hset]
  rw [coordinate_measurePreserving.measure_preimage (measurableSet_Icc.nullMeasurableSet)]
  rw [Measure.restrict_apply measurableSet_Icc]
  have hsub : Set.Icc (-a/20) (a/20) ⊆ Set.Ioc (-(1 : ℝ)/2) (1/2) := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioc]
    constructor <;> linarith [hx.1, hx.2]
  rw [Set.inter_eq_left.mpr hsub, Real.volume_Icc]
  congr 1
  ring


theorem cdf_below (a : ℝ) (ha : a < 0) :
    haarAddCircle {x : AddCircle (1 : ℝ) | position x ≤ a} = 0 := by
  have he : {x : AddCircle (1 : ℝ) | position x ≤ a} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    have h := (position_mem x).1
    linarith
  simp [he]

theorem cdf_above (a : ℝ) (ha : 10 ≤ a) :
    haarAddCircle {x : AddCircle (1 : ℝ) | position x ≤ a} = 1 := by
  have he : {x : AddCircle (1 : ℝ) | position x ≤ a} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (position_mem x).2.trans ha
  simp [he]

theorem position_distribution :
    Measure.map position (haarAddCircle (T := (1 : ℝ))) =
      ENNReal.ofReal (1/10 : ℝ) • volume.restrict (Set.Ioo (0 : ℝ) 10) := by
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply position_measurable measurableSet_Iic, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic]
  change haarAddCircle {x : AddCircle (1 : ℝ) | position x ≤ a} = _
  by_cases h0 : a < 0
  · rw [cdf_below a h0]
    have he : Set.Iic a ∩ Set.Ioo (0 : ℝ) 10 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx, hx0, _⟩
      linarith
    simp [he]
  · have h0' : 0 ≤ a := le_of_not_gt h0
    by_cases h10 : a < 10
    · rw [cdf_inside a h0' h10]
      have he : Set.Iic a ∩ Set.Ioo (0 : ℝ) 10 = Set.Ioc 0 a := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo, Set.mem_Ioc]
        constructor
        · rintro ⟨hx, hx0, _⟩
          exact ⟨hx0, hx⟩
        · rintro ⟨hx0, hx⟩
          exact ⟨hx, hx0, lt_of_le_of_lt hx h10⟩
      rw [he, Real.volume_Ioc]
      simp only [sub_zero, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/10)]
      congr 1
      ring
    · have h10' : 10 ≤ a := le_of_not_gt h10
      rw [cdf_above a h10']
      have he : Set.Iic a ∩ Set.Ioo (0 : ℝ) 10 = Set.Ioo 0 10 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo]
        constructor
        · exact fun h => h.2
        · rintro ⟨hx0, hx10⟩
          exact ⟨le_trans (le_of_lt hx10) h10', hx0, hx10⟩
      rw [he, Real.volume_Ioo]
      simp only [sub_zero, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/10)]
      norm_num


def normalizedIntervalMeasure : Measure ℝ :=
  ENNReal.ofReal (1/10 : ℝ) • volume.restrict (Set.Ioo (0 : ℝ) 10)

theorem position_measurePreserving :
    MeasurePreserving position (haarAddCircle (T := (1 : ℝ))) normalizedIntervalMeasure :=
  ⟨position_measurable, position_distribution⟩

def pullback : Lp ℝ 2 normalizedIntervalMeasure →ₗᵢ[ℝ] Lp ℝ 2 (haarAddCircle (T := (1 : ℝ))) :=
  Lp.compMeasurePreservingₗᵢ ℝ position position_measurePreserving

theorem pullback_norm (f : Lp ℝ 2 normalizedIntervalMeasure) : ‖pullback f‖ = ‖f‖ :=
  pullback.norm_map f

theorem pullback_ae (f : Lp ℝ 2 normalizedIntervalMeasure) :
    (pullback f : AddCircle (1 : ℝ) → ℝ) =ᵐ[haarAddCircle] fun x => f (position x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem pullback_injective : Function.Injective pullback := pullback.injective

end HeatFoldProbability
#check @HeatFoldProbability.cdf_inside
#print axioms HeatFoldProbability.cdf_inside

#check @HeatFoldProbability.cdf_below
#print axioms HeatFoldProbability.cdf_below
#check @HeatFoldProbability.cdf_above
#print axioms HeatFoldProbability.cdf_above
#check @HeatFoldProbability.position_distribution
#print axioms HeatFoldProbability.position_distribution

#check @HeatFoldProbability.position_measurePreserving
#print axioms HeatFoldProbability.position_measurePreserving
#check @HeatFoldProbability.pullback_norm
#print axioms HeatFoldProbability.pullback_norm
#check @HeatFoldProbability.pullback_ae
#print axioms HeatFoldProbability.pullback_ae
#check @HeatFoldProbability.pullback_injective
#print axioms HeatFoldProbability.pullback_injective
