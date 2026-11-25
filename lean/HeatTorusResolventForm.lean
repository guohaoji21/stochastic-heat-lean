import HeatTorusGradient
import HeatTorusResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusResolventForm

open MeasureTheory Filter Set UnitAddTorus HeatTorusFourier HeatTorusReal HeatTorusGradient
open scoped NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

theorem inner_realPart_embed (z : State ι) (v : RealState ι) :
    (inner ℂ z (embed v)).re = inner ℝ (realPart z) v := by
  rw [L2.inner_def, L2.inner_def]
  change Complex.reCLM (∫ x, inner ℂ (z x) (embed v x)) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner z (embed v))]
  apply integral_congr_ae
  filter_upwards [realPart_ae z, embed_ae v] with x hz hv
  rw [hz, hv]
  simp [mul_comm]

/-- The Fourier resolvent has an (L²) gradient and solves the exact
variational equation, with the frequency scaling of the physical period. -/
theorem variational (P : ℝ) (a : ℝ≥0) (ha : 0 < a) (f : RealState ι) :
    ∃ D : ι → State ι, HasGradient P (embed (HeatTorusResolvent.step P a f)) D ∧
      ∀ (v : RealState ι) (Q : ι → State ι), HasGradient P (embed v) Q →
        inner ℝ (HeatTorusResolvent.step P a f) v + (a : ℝ) * ∑ i, (inner ℂ (D i) (Q i)).re =
          inner ℝ f v := by
  let u := HeatTorusResolvent.step P a f
  let g := (a : ℝ)⁻¹ • (u - f)
  have hreal := HeatTorusResolvent.generator_step P a ha f
  have hgen := (generator_iff_coefficients P (embed u) (embed g)).mpr
    ((HeatTorusSubeigen.generator_iff_coefficients P u g).mp hreal)
  obtain ⟨D, hD⟩ := exists_gradient_of_generator P (embed u) (embed g) hgen
  refine ⟨D, hD, ?_⟩
  intro v Q hQ
  have hform := real_generator_inner_eq_gradient P u g v D Q hreal hD hQ
  have ha' : (a : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
  have h := congrArg (fun y : ℝ => (a : ℝ) * y) hform
  change (a : ℝ) * inner ℝ ((a : ℝ)⁻¹ • (u - f)) v = _ at h
  simp only [real_inner_smul_left, inner_sub_left, ← mul_assoc, mul_inv_cancel₀ ha', one_mul,
    mul_neg] at h
  change inner ℝ u v + (a : ℝ) * ∑ i, (inner ℂ (D i) (Q i)).re = _
  linarith only [h]

/-- Restricting to real test gradients expresses the Dirichlet form with
real (L²) inner products. -/
theorem variational_real_tests (P : ℝ) (a : ℝ≥0) (ha : 0 < a) (f : RealState ι) :
    ∃ D : ι → State ι, HasGradient P (embed (HeatTorusResolvent.step P a f)) D ∧
      ∀ (v : RealState ι) (Q : ι → RealState ι), HasGradient P (embed v) (fun i => embed (Q i)) →
        inner ℝ (HeatTorusResolvent.step P a f) v +
          (a : ℝ) * ∑ i, inner ℝ (realPart (D i)) (Q i) = inner ℝ f v := by
  obtain ⟨D, hD, h⟩ := variational P a ha f
  refine ⟨D, hD, fun v Q hQ => ?_⟩
  simpa only [inner_realPart_embed] using h v (fun i => embed (Q i)) hQ

/-- Passing to unit-period coordinates divides the resolvent step size by
the square of the physical period. -/
theorem step_unit_coordinates (P : ℝ) (a : ℝ≥0) (f : RealState ι) :
    HeatTorusResolvent.step P a f =
      HeatTorusResolvent.step 1 (a / Real.toNNReal (P ^ 2)) f := by
  apply (Function.LeftInverse.injective (realPart_embed (ι := ι)))
  apply (mFourierBasis (d := ι)).repr.injective
  apply lp.ext
  funext k
  simp only [mFourierBasis_repr, HeatTorusResolvent.coefficient_step, NNReal.coe_div,
    Real.coe_toNNReal _ (sq_nonneg P)]
  have hf : frequencySquared P k = frequencySquared 1 k / P ^ 2 := by
    unfold frequencySquared
    rw [div_one, div_pow, div_mul_eq_mul_div]
  have he : (a : ℝ) * frequencySquared P k = (a : ℝ) / P ^ 2 * frequencySquared 1 k := by
    rw [hf]
    simp only [div_eq_mul_inv]
    ring
  rw [he]

end HeatTorusResolventForm

#print axioms HeatTorusResolventForm.inner_realPart_embed
#print axioms HeatTorusResolventForm.variational
#print axioms HeatTorusResolventForm.variational_real_tests
#print axioms HeatTorusResolventForm.step_unit_coordinates
