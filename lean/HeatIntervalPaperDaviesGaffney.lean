import HeatDaviesGaffney

set_option autoImplicit false
noncomputable section

namespace HeatIntervalPaperDaviesGaffney

open MeasureTheory Filter Set HeatIntervalNormalization HeatRestrictionAdjoint

local notation "A" => Ioo (1 : ℝ) 2
local notation "D" => Ioo (6 : ℝ) 7

theorem separation : sInf ((fun p : ℝ × ℝ => dist p.1 p.2) '' (A ×ˢ D)) = 4 := by
  let S := (fun p : ℝ × ℝ => dist p.1 p.2) '' (A ×ˢ D)
  have hbound : ∀ z ∈ S, 4 ≤ z := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    change x ∈ A at hx
    change y ∈ D at hy
    change 4 ≤ dist x y
    rw [Real.dist_eq, abs_of_neg (by linarith [hx.2, hy.1] : x-y < 0)]
    linarith [hx.2, hy.1]
  have hn : S.Nonempty := ⟨dist (3/2 : ℝ) (13/2), (3/2, 13/2), by norm_num [mem_prod], rfl⟩
  apply le_antisymm _ (le_csInf hn hbound)
  by_contra! hlt
  let ε := min (1/2 : ℝ) ((sInf S - 4) / 4)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε₁ : ε ≤ 1/2 := min_le_left _ _
  have hε₂ : ε ≤ (sInf S - 4) / 4 := min_le_right _ _
  have hx : (2-ε : ℝ) ∈ A := ⟨by linarith, by linarith⟩
  have hy : (6+ε : ℝ) ∈ D := ⟨by linarith, by linarith⟩
  have h := csInf_le ⟨4, hbound⟩
    (show dist (2-ε : ℝ) (6+ε) ∈ S from ⟨(2-ε, 6+ε), ⟨hx, hy⟩, rfl⟩)
  rw [Real.dist_eq, abs_of_neg (by linarith : (2-ε)-(6+ε) < 0)] at h
  linarith

def indicatorMultiplier : Base →L[ℝ] Base :=
  (adjointExtension baseMeasure D).comp (restriction baseMeasure D)

/-- Restriction to `(1,2)` after heat evolution from data supported in `(6,7)`. -/
theorem operator_norm (t : ℝ) (ht : 0 < t) :
    ‖((paperBstar.comp (paperHeat t)).comp indicatorMultiplier)‖ ≤ Real.exp (-4/t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro f
  have he := adjointExtension_ae baseMeasure D measurableSet_Ioo (restriction baseMeasure D f)
  have hf := (ae_restrict_iff' measurableSet_Ioo).mp (restriction_ae baseMeasure D f)
  have hs : ∀ᵐ x ∂baseMeasure, x ∉ D → indicatorMultiplier f x = 0 := by
    filter_upwards [he] with x h hx
    change adjointExtension baseMeasure D (restriction baseMeasure D f) x = 0
    rw [h, indicator_of_notMem hx]
  have hnorm : ‖indicatorMultiplier f‖ ≤ ‖f‖ := by
    rw [← one_mul ‖f‖]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [he, hf] with x h hr
    change ‖adjointExtension baseMeasure D (restriction baseMeasure D f) x‖ ≤ 1 * ‖f x‖
    rw [h, one_mul]
    by_cases hx : x ∈ D
    · rw [indicator_of_mem hx, hr hx]
    · rw [indicator_of_notMem hx, norm_zero]
      exact norm_nonneg _
  exact (HeatDaviesGaffney.bound t ht (indicatorMultiplier f) hs).trans
    (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)

end HeatIntervalPaperDaviesGaffney

#print axioms HeatIntervalPaperDaviesGaffney.separation
#print axioms HeatIntervalPaperDaviesGaffney.operator_norm
