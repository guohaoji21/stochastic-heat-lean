import HeatSubintervalMass

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section

namespace HeatSmallIntervalAffine

open MeasureTheory Set HeatIntervalNormalization HeatSubintervalMass
open scoped ENNReal

/-- The affine coordinate that sends the plateau interval to `(0, 10)`. -/
def toLarge : ℝ ≃ᵐ ℝ :=
  (MeasurableEquiv.addRight (-(25 / 4 : ℝ))).trans
    (MeasurableEquiv.mulLeft₀ (20 : ℝ) (by norm_num))

theorem toLarge_apply (x : ℝ) : toLarge x = 20 * (x - 25 / 4) := by
  simp only [toLarge, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_addRight,
    MeasurableEquiv.coe_mulLeft₀, sub_eq_add_neg]

theorem preimage_large : toLarge ⁻¹' Ioo (0 : ℝ) 10 = plateau := by
  ext x
  simp only [mem_preimage, toLarge_apply, mem_Ioo, plateau]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem map_volume : Measure.map toLarge (volume : Measure ℝ) =
    ENNReal.ofReal (1 / 20 : ℝ) • volume := by
  have ha : Measurable (fun x : ℝ => x + -(25 / 4 : ℝ)) := measurable_id.add measurable_const
  have hm : Measurable (fun x : ℝ => 20 * x) := measurable_const.mul measurable_id
  have he : (toLarge : ℝ → ℝ) = (fun x : ℝ => 20 * x) ∘ (fun x : ℝ => x + -(25 / 4 : ℝ)) := rfl
  rw [he, ← Measure.map_map hm ha, (measurePreserving_add_right volume (-(25 / 4 : ℝ))).map_eq,
    Real.map_volume_mul_left (by norm_num : (20 : ℝ) ≠ 0)]
  norm_num

/-- Change of variables for the actual unnormalized measures used by the two
Dirichlet state spaces. The factor is the reciprocal spatial dilation. -/
theorem map_subinterval : Measure.map toLarge (baseMeasure.restrict plateau) =
    ENNReal.ofReal (1 / 20 : ℝ) • baseMeasure := by
  have hsub : plateau ⊆ Ioo (0 : ℝ) 10 := by
    intro x hx
    have h : x ∈ Ioo (25 / 4 : ℝ) (27 / 4 : ℝ) := hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hme : baseMeasure.restrict plateau = (volume : Measure ℝ).restrict plateau :=
    Measure.restrict_restrict_of_subset hsub
  rw [hme]
  ext s hs
  rw [Measure.map_apply toLarge.measurable hs, Measure.restrict_apply (toLarge.measurable hs),
    ← preimage_large, ← Set.preimage_inter,
    ← Measure.map_apply toLarge.measurable (hs.inter measurableSet_Ioo), map_volume,
    Measure.smul_apply, Measure.smul_apply]
  rw [baseMeasure, Measure.restrict_apply hs]

end HeatSmallIntervalAffine

#print axioms HeatSmallIntervalAffine.map_subinterval
