import HeatTorusGaussian
import HeatRestrictionAdjoint
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Probability.Moments.SubGaussian

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatTorusOffDiagonal

open MeasureTheory ProbabilityTheory HeatTorusGaussian HeatTorusReal UnitAddTorus Set Filter
open scoped NNReal ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι]

private theorem real_tail (v : ℝ≥0) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussianReal 0 v).real {x | δ ≤ |x|} ≤ 2 * Real.exp (-δ^2 / (2*v)) := by
  have h : HasSubgaussianMGF id v (gaussianReal 0 v) := by
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
    simp [mgf_id_gaussianReal]
  have hpos := h.measure_ge_le hδ
  have hneg := h.neg.measure_ge_le hδ
  have hincl : {x : ℝ | δ ≤ |x|} ⊆ {x | δ ≤ x} ∪ {x | δ ≤ -x} := by
    intro x hx
    change δ ≤ |x| at hx
    rcases le_or_gt 0 x with h₀ | h₀
    · exact Or.inl (show δ ≤ x by rwa [abs_of_nonneg h₀] at hx)
    · exact Or.inr (show δ ≤ -x by rwa [abs_of_neg h₀] at hx)
  calc
    _ ≤ (gaussianReal 0 v).real ({x | δ ≤ x} ∪ {x | δ ≤ -x}) := measureReal_mono hincl
    _ ≤ (gaussianReal 0 v).real {x | δ ≤ x} + (gaussianReal 0 v).real {x | δ ≤ -x} := measureReal_union_le _ _
    _ ≤ _ := by rw [two_mul]; exact add_le_add hpos hneg

theorem increment_tail (P t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (increment (ι := ι) P t).real {z | δ ≤ dist z 0} ≤
      (2 * (Fintype.card ι : ℝ)) * Real.exp (-δ^2 / (2 * variance P t)) := by
  let ν : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 (variance P t))
  let A : ι → Set (ι → ℝ) := fun i => {x | δ ≤ |x i|}
  have hpre : wrap (ι := ι) ⁻¹' {z | δ ≤ dist z 0} ⊆ ⋃ i, A i := by
    intro x hx
    by_contra h
    have hc (i : ι) : |x i| < δ := lt_of_not_ge fun hi => h (mem_iUnion.mpr ⟨i, hi⟩)
    have hx' : dist (wrap x) 0 < δ := (dist_pi_lt_iff hδ).mpr fun i => by
      rw [Pi.zero_apply, dist_zero_right]
      exact ((QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x i)).trans_lt
        (by simpa only [Real.norm_eq_abs] using hc i))
    exact (not_lt_of_ge hx) hx'
  have ha : ∀ i, ν.real (A i) ≤ 2 * Real.exp (-δ^2 / (2 * variance P t)) := by
    intro i
    have he := (measurePreserving_eval (μ := fun _ : ι => gaussianReal 0 (variance P t)) i).map_eq
    have hset : MeasurableSet {x : ℝ | δ ≤ |x|} := isClosed_le continuous_const continuous_abs |>.measurableSet
    have heq : ν (A i) = gaussianReal 0 (variance P t) {x | δ ≤ |x|} := by
      change ν ((Function.eval i) ⁻¹' {x : ℝ | δ ≤ |x|}) = _
      rw [← Measure.map_apply (measurable_pi_apply i) hset]
      exact congrArg (fun μ : Measure ℝ => μ {x | δ ≤ |x|}) he
    exact (congrArg ENNReal.toReal heq).trans_le (real_tail _ hδ.le)
  have hset : MeasurableSet {z : UnitAddTorus ι | δ ≤ dist z 0} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  calc
    _ = ν.real (wrap ⁻¹' {z | δ ≤ dist z 0}) := by
      rw [increment, Measure.real, Measure.map_apply continuous_wrap.measurable hset]
      rfl
    _ ≤ ν.real (⋃ i, A i) := measureReal_mono hpre
    _ ≤ ∑ i, ν.real (A i) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ _ : ι, 2 * Real.exp (-δ^2 / (2 * variance P t)) := Finset.sum_le_sum fun i _ => ha i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

private theorem restriction_shift_zero (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    {δ : ℝ} (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y) (f : RealState ι)
    (hf : ∀ᵐ x ∂volume, x ∉ D → f x = 0) (z : UnitAddTorus ι) (hz : dist z 0 < δ) :
    HeatRestrictionAdjoint.restriction volume O (shift f z) = 0 := by
  apply Lp.ext
  filter_upwards [HeatRestrictionAdjoint.restriction_ae volume O (shift f z),
    ae_restrict_of_ae (shift_ae f z),
    ae_restrict_of_ae ((translation_preserving z).quasiMeasurePreserving.ae hf),
    ae_restrict_mem hO, Lp.coeFn_zero ℝ 2 (volume.restrict O)] with x hr hs hfx hx hz₀
  rw [hr, hs, hz₀]
  apply hfx
  intro hxD
  have he : dist x (x+z) = dist z 0 := by
    rw [dist_comm, dist_eq_norm, dist_zero_right, add_sub_cancel_left]
  exact (not_le_of_gt hz) (he ▸ hsep x hx (x+z) hxD)

/-- Gaussian off-diagonal bound for the periodic heat semigroup. The
finite dimensional prefactor comes from taking a union over coordinates. -/
theorem restriction_heat_bound (P t : ℝ) (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y) (f : RealState ι)
    (hf : ∀ᵐ x ∂volume, x ∉ D → f x = 0) :
    ‖HeatRestrictionAdjoint.restriction volume O (realHeat P t f)‖ ≤
      (2 * (Fintype.card ι : ℝ)) * Real.exp (-δ^2 / (2 * variance P t)) * ‖f‖ := by
  let B := HeatRestrictionAdjoint.restriction (volume : Measure (UnitAddTorus ι)) O
  let A := {z : UnitAddTorus ι | δ ≤ dist z 0}
  let μ := increment (ι := ι) P t
  have hA : MeasurableSet A := (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  have hB (x : RealState ι) : ‖B x‖ ≤ ‖x‖ := norm_Lp_toLp_restrict_le O x
  have hi : Integrable (fun z => B (shift f z)) μ := B.integrable_comp (integrable_shift P t f)
  have hdom (z : UnitAddTorus ι) : ‖B (shift f z)‖ ≤ A.indicator (fun _ => ‖f‖) z := by
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz, ← shift_norm f z]
      exact hB _
    · rw [indicator_of_notMem hz, restriction_shift_zero O D hO hsep f hf z (lt_of_not_ge hz), norm_zero]
  change ‖B (realHeat P t f)‖ ≤ _
  rw [realHeat_eq_integral_shift, ← B.integral_comp_comm (integrable_shift P t f)]
  calc
    _ ≤ ∫ z, ‖B (shift f z)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, A.indicator (fun _ => ‖f‖) z ∂μ :=
      integral_mono hi.norm ((integrable_const _).indicator hA) hdom
    _ = μ.real A * ‖f‖ := by rw [integral_indicator hA, setIntegral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (increment_tail P t hδ) (norm_nonneg _)

/-- The form used on a time cell, including evolution for zero time.
The separation `δ` is in unit coordinates and the physical period is `P`. -/
theorem restriction_heat_time_bound {P t L : ℝ} (hP : 0 < P) (hL : 0 < L)
    (ht : 0 ≤ t) (htL : t ≤ L) (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y) (f : RealState ι)
    (hf : ∀ᵐ x ∂volume, x ∉ D → f x = 0) :
    ‖HeatRestrictionAdjoint.restriction volume O (realHeat P t f)‖ ≤
      (2 * (Fintype.card ι : ℝ)) * Real.exp (-(δ^2 * P^2) / (4*L)) * ‖f‖ := by
  rcases ht.eq_or_lt with he | htp
  · subst t
    rw [realHeat_zero, ContinuousLinearMap.id_apply]
    have hz : shift f 0 = f := by
      apply Lp.ext
      simpa only [add_zero] using shift_ae f 0
    have hb := restriction_shift_zero O D hO hsep f hf 0 (by simpa using hδ)
    rw [hz] at hb
    rw [hb, norm_zero]
    positivity
  · have hv : (variance P t : ℝ) = 2*t/P^2 := by
      unfold HeatTorusGaussian.variance
      rw [max_eq_left ht, Real.coe_toNNReal _ (by positivity)]
    have hexp : -δ^2 / (2 * variance P t : ℝ) = -(δ^2*P^2)/(4*t) := by
      rw [hv]
      field_simp
      <;> ring
    apply (restriction_heat_bound P t O D hO hδ hsep f hf).trans
    rw [hexp]
    have hdiv : δ^2 * P^2 / (4*L) ≤ δ^2 * P^2 / (4*t) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left htL (by norm_num))
    have hneg : -(δ^2 * P^2) / (4*t) ≤ -(δ^2 * P^2) / (4*L) := by
      rw [neg_div, neg_div]
      exact neg_le_neg hdiv
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) (by positivity)) (norm_nonneg _)

end HeatTorusOffDiagonal

#print axioms HeatTorusOffDiagonal.increment_tail
#print axioms HeatTorusOffDiagonal.restriction_heat_bound
#print axioms HeatTorusOffDiagonal.restriction_heat_time_bound
