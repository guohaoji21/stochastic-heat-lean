import HeatFlatTorusDistanceWeight
import HeatTorusSmoothWeight
import HeatRestrictionAdjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusDaviesGaffney

open MeasureTheory Set Filter UnitAddTorus HeatTorusReal HeatTorusSmoothWeight
open HeatTorusInitialData (rescale)
open HeatFlatTorusDistance (distance distanceTo distanceTo_eq_zero le_distanceTo)
open HeatRestrictionAdjoint (restriction restriction_ae)
open scoped NNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem distance_weight_bound {P α ε δ : ℝ} (hP : 0 < P) (hα : 0 ≤ α) (hε : 0 < ε)
    (A : Set (UnitAddTorus ι)) (hA : MeasurableSet A) {D : Set (ι → AddCircle P)}
    (hD : D.Nonempty) (hsep : ∀ x ∈ A, ∀ y ∈ D, δ ≤ distance (rescale hP x) y)
    (t : ℝ≥0) (f : RealState ι) (hf : ∀ᵐ x ∂volume, rescale hP x ∉ D → f x = 0) :
    ‖restriction volume A (realHeat P t f)‖ ≤
      Real.exp ((t : ℝ) * α ^ 2 - α * δ + 2 * α * ε) * ‖f‖ := by
  obtain ⟨φ, dφ, herr, hgrad, hd⟩ :=
    HeatFlatTorusDistanceWeight.exists_distance_approx hP hε hD
  let w : C(UnitAddTorus ι, ℝ) :=
    ⟨fun x => Real.exp (α * φ x), Real.continuous_exp.comp (continuous_const.mul φ.continuous)⟩
  let dw (i : ι) : C(UnitAddTorus ι, ℝ) :=
    ⟨fun x => (α * w x) * dφ i x, (continuous_const.mul w.continuous).mul (dφ i).continuous⟩
  have hderiv (i : ι) (x : UnitAddTorus ι) (s : ℝ) :
      HasDerivAt (fun r : ℝ => w (x + Pi.single i (r : UnitAddCircle)))
        (P * dw i (x + Pi.single i (s : UnitAddCircle))) s := by
    convert ((hd i x s).const_mul α).exp using 1
    change P * ((α * Real.exp _) * dφ i (x + Pi.single i (s : UnitAddCircle))) =
      Real.exp _ * (α * (P * dφ i (x + Pi.single i (s : UnitAddCircle))))
    ring
  have hw (x : UnitAddTorus ι) : ∑ i, (dw i x) ^ 2 ≤ α ^ 2 * (w x) ^ 2 := by
    change ∑ i, ((α * w x) * dφ i x) ^ 2 ≤ _
    simp_rw [mul_pow, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hgrad x) (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq
      (mul_one _)
  have hinput : ‖weight w f‖ ≤ Real.exp (α * ε) * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [weight_ae w f, hf] with x hfw hs
    rw [hfw, norm_mul]
    by_cases hx : rescale hP x ∈ D
    · change ‖Real.exp (α * φ x)‖ * ‖f x‖ ≤ _
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left _ hα)
      simpa only [distanceTo_eq_zero hx, sub_zero] using (abs_le.mp (herr x)).2
    · simp [hs hx]
  let u := realHeat P t f
  have hpoint : ∀ᵐ x ∂(volume.restrict A : Measure (UnitAddTorus ι)),
      ‖restriction volume A u x‖ ≤
        Real.exp (-α * (δ - ε)) * ‖restriction volume A (weight w u) x‖ := by
    filter_upwards [restriction_ae volume A u, restriction_ae volume A (weight w u),
      (weight_ae w u).filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem hA]
      with x h₁ h₂ h₃ hx
    rw [h₁, h₂, h₃, norm_mul]
    change ‖u x‖ ≤ Real.exp (-α * (δ - ε)) * (‖Real.exp (α * φ x)‖ * ‖u x‖)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
    apply le_trans (one_mul ‖u x‖).symm.le
    refine mul_le_mul_of_nonneg_right (Real.one_le_exp_iff.mpr ?_) (norm_nonneg _)
    have hd' := le_distanceTo hD (rescale hP x) (hsep x hx)
    have hl := (abs_le.mp (herr x)).1
    have hx' : 0 ≤ φ x - (δ - ε) := by linarith
    have he := mul_nonneg hα hx'
    linarith
  calc
    _ ≤ Real.exp (-α * (δ - ε)) * ‖restriction volume A (weight w u)‖ :=
      Lp.norm_le_mul_norm_of_ae_le_mul hpoint
    _ ≤ Real.exp (-α * (δ - ε)) * ‖weight w u‖ :=
      mul_le_mul_of_nonneg_left (norm_Lp_toLp_restrict_le A _) (Real.exp_pos _).le
    _ ≤ Real.exp (-α * (δ - ε)) * (Real.exp ((t : ℝ) * α ^ 2) * ‖weight w f‖) :=
      mul_le_mul_of_nonneg_left (heat_bound hP.ne' w dw hderiv hw t f) (Real.exp_pos _).le
    _ ≤ Real.exp (-α * (δ - ε)) *
        (Real.exp ((t : ℝ) * α ^ 2) * (Real.exp (α * ε) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinput (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by
      simp only [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Davies–Gaffney with constant one for the physical flat-torus distance. -/
theorem restriction_heat {P δ : ℝ} (hP : 0 < P) (hδ : 0 ≤ δ)
    (A : Set (UnitAddTorus ι)) (hA : MeasurableSet A) (D : Set (ι → AddCircle P))
    (hsep : ∀ x ∈ A, ∀ y ∈ D, δ ≤ distance (rescale hP x) y)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (f : RealState ι)
    (hf : ∀ᵐ x ∂volume, rescale hP x ∉ D → f x = 0) :
    ‖restriction volume A (realHeat P t f)‖ ≤ Real.exp (-δ ^ 2 / (4 * (t : ℝ))) * ‖f‖ := by
  classical
  by_cases hD : D.Nonempty
  · let α := δ / (2 * (t : ℝ))
    have hα : 0 ≤ α := div_nonneg hδ (by positivity)
    have hc : Continuous (fun ε : ℝ => Real.exp ((t : ℝ) * α ^ 2 - α * δ + 2 * α * ε) * ‖f‖) :=
      by fun_prop
    have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖restriction volume A (realHeat P t f)‖ ≤
        Real.exp ((t : ℝ) * α ^ 2 - α * δ + 2 * α * ε) * ‖f‖ := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact distance_weight_bound hP hα hε A hA hD hsep t f hf
    have hh := ge_of_tendsto (hc.continuousAt.continuousWithinAt.tendsto) hb
    simp only [mul_zero, add_zero] at hh
    refine hh.trans_eq ?_
    congr 2
    dsimp only [α]
    field_simp [ne_of_gt ht]
    <;> ring
  · have hz : f = 0 := by
      apply Lp.ext
      filter_upwards [hf, Lp.coeFn_zero ℝ 2 (volume : Measure (UnitAddTorus ι))] with x h₁ h₂
      rw [h₂, Pi.zero_apply, h₁ (fun hx => hD ⟨_, hx⟩)]
    simp [hz]

end HeatTorusDaviesGaffney

#print axioms HeatTorusDaviesGaffney.restriction_heat
