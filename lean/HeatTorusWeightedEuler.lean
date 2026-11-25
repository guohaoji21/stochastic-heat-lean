import HeatTorusEuler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace HeatTorusWeightedEuler

open Filter MeasureTheory Set HeatTorusReal
open scoped Topology NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]
variable (P c : ℝ) (W : RealState ι →L[ℝ] RealState ι)
  (hform : ∀ u g : RealState ι,
    HasDerivWithinAt (fun t : ℝ => realHeat P t u) g (Ici 0) 0 →
    inner ℝ (W g) (W u) ≤ c * ‖W u‖ ^ 2)

include hform in
theorem step_bound (a : ℝ≥0) (ha : 0 < a) (hac : 0 < 1 - (a : ℝ) * c) (f : RealState ι) :
    ‖W (HeatTorusResolvent.step P a f)‖ ≤ (1 - (a : ℝ) * c)⁻¹ * ‖W f‖ := by
  let u := HeatTorusResolvent.step P a f
  let g := (a : ℝ)⁻¹ • (u - f)
  have hg := hform u g (HeatTorusResolvent.generator_step P a ha f)
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
  have hu : u = f + (a : ℝ) • g := by
    change u = f + (a : ℝ) • ((a : ℝ)⁻¹ • (u - f))
    rw [smul_smul, mul_inv_cancel₀ ha', one_smul, add_sub_cancel]
  have hW : W u = W f + (a : ℝ) • W g := by
    conv_lhs => rw [hu]
    rw [map_add, map_smul]
  have henergy : ‖W u‖ ^ 2 ≤ ‖W f‖ * ‖W u‖ + (a : ℝ) * (c * ‖W u‖ ^ 2) := by
    calc
      _ = inner ℝ (W u) (W u) := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ (W f) (W u) + (a : ℝ) * inner ℝ (W g) (W u) := by
        conv_lhs => arg 2; rw [hW]
        rw [inner_add_left, real_inner_smul_left]
      _ ≤ _ := add_le_add (real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left hg a.property)
  change ‖W u‖ ≤ _
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hac).mpr
  by_cases hz : ‖W u‖ = 0
  · rw [hz, zero_mul]
    exact norm_nonneg _
  · have hpos : 0 < ‖W u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [henergy]

include hform in
private theorem iterate_bound (a : ℝ≥0) (ha : 0 < a) (hac : 0 < 1 - (a : ℝ) * c)
    (f : RealState ι) (n : ℕ) :
    ‖W (((HeatTorusResolvent.step P a : RealState ι → RealState ι)^[n]) f)‖ ≤
      ((1 - (a : ℝ) * c)⁻¹) ^ n * ‖W f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine (step_bound P c W hform a ha hac _).trans ?_
    exact (mul_le_mul_of_nonneg_left ih (inv_nonneg.mpr hac.le)).trans_eq
      (by rw [pow_succ', mul_assoc])

include hform in
/-- A generator energy inequality in the weighted norm propagates to the
actual torus heat semigroup with the same exponential rate. -/
theorem heat_bound (T : ℝ≥0) (f : RealState ι) :
    ‖W (realHeat P T f)‖ ≤ Real.exp ((T : ℝ) * c) * ‖W f‖ := by
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from zero_le) with hT | hT
  · subst T
    simp [realHeat_zero]
  have hLeft := (W.continuous.continuousAt.tendsto.comp (HeatTorusEuler.tendsto_heat P T f)).norm
  have hRight := (HeatEulerScalar.tendsto_inverse (-((T : ℝ) * c))).mul_const ‖W f‖
  simp only [neg_neg] at hRight
  apply le_of_tendsto_of_tendsto hLeft hRight
  have hbig : ∀ᶠ n : ℕ in atTop, max ((T : ℝ) * c) 0 < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  filter_upwards [hbig] with n hn
  have hn' : (0 : ℝ) < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hn₀ : 0 < (n : ℝ≥0) := by exact_mod_cast hn'
  have ha : 0 < T / (n : ℝ≥0) := div_pos hT hn₀
  have heq : 1 - ((T / (n : ℝ≥0) : ℝ≥0) : ℝ) * c = 1 + -((T : ℝ) * c) / (n : ℝ) := by
    push_cast
    ring
  have hpos : 0 < 1 - ((T / (n : ℝ≥0) : ℝ≥0) : ℝ) * c := by
    rw [heq, neg_div, ← sub_eq_add_neg]
    exact sub_pos.mpr ((div_lt_iff₀ hn').mpr (by simpa using (le_max_left _ _).trans_lt hn))
  simpa only [Function.comp_def, heq] using iterate_bound P c W hform _ ha hpos f n

end HeatTorusWeightedEuler

#print axioms HeatTorusWeightedEuler.heat_bound
