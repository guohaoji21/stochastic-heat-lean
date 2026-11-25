import HeatTorusGradientProduct
import HeatTorusRealIntertwining
import HeatTorusWeightedEuler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section

namespace HeatTorusSmoothWeight

open MeasureTheory Filter Set UnitAddTorus HeatTorusFourier HeatTorusReal HeatTorusGradient
open HeatTorusGalerkinCompression (fullMultiplier fullMultiplier_ae)
open scoped ComplexConjugate NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def asComplex (w : C(UnitAddTorus ι, ℝ)) : C(UnitAddTorus ι, ℂ) :=
  ⟨fun x => (w x : ℂ), Complex.continuous_ofReal.comp w.continuous⟩

def weight (w : C(UnitAddTorus ι, ℝ)) : RealState ι →L[ℝ] RealState ι :=
  HeatTorusRealIntertwining.multiplier (asComplex w)

omit [DecidableEq ι] in
theorem weight_ae (w : C(UnitAddTorus ι, ℝ)) (u : RealState ι) :
    (weight w u : UnitAddTorus ι → ℝ) =ᵐ[volume] fun x => w x * u x := by
  filter_upwards [HeatTorusRealIntertwining.multiplier_ae (asComplex w) u] with x hx
  change weight w u x = (w x : ℂ).re * u x at hx
  rwa [Complex.ofReal_re] at hx

private theorem embed_weight (w : C(UnitAddTorus ι, ℝ)) (u : RealState ι) :
    embed (weight w u) = fullMultiplier (asComplex w) (embed u) := by
  apply Lp.ext
  filter_upwards [embed_ae (weight w u), weight_ae w u,
    fullMultiplier_ae (asComplex w) (embed u), embed_ae u] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  exact Complex.ofReal_mul _ _

private theorem inner_weight (w : C(UnitAddTorus ι, ℝ)) (u g : RealState ι) :
    inner ℝ (weight w g) (weight w u) = inner ℝ g (weight (w * w) u) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weight_ae w g, weight_ae w u, weight_ae (w * w) u] with x hg hu h₂
  rw [hg, hu, h₂]
  simp only [Real.inner_apply, ContinuousMap.mul_apply]
  ring

private theorem integrated_square (w : C(UnitAddTorus ι, ℝ)) (u : RealState ι) :
    ‖weight w u‖ ^ 2 = ∫ x, (w x * u x) ^ 2 := by
  rw [HeatIntervalNormalization.realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [weight_ae w u] with x hx
  rw [Real.norm_eq_abs, sq_abs, hx]

private theorem integrable_square (w : C(UnitAddTorus ι, ℝ)) (u : RealState ι) :
    Integrable (fun x => (w x * u x) ^ 2) volume := by
  have h : Integrable (fun x => (weight w u x) ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using (Lp.memLp (weight w u)).norm.integrable_sq
  exact h.congr ((weight_ae w u).fun_comp (fun y : ℝ => y ^ 2))

private theorem coordinate_energy (w d : ℝ) (u p : ℂ) :
    -(inner ℂ p (((2 * w * d : ℝ) : ℂ) * u + ((w * w : ℝ) : ℂ) * p)).re ≤
      d ^ 2 * Complex.normSq u := by
  have h := Complex.normSq_nonneg ((w : ℂ) * p + (d : ℂ) * u)
  simp only [RCLike.inner_apply, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at h ⊢
  nlinarith only [h]

/-- The Davies energy inequality for multiplication by a smooth real
weight, assuming the pointwise squared gradient bound in physical units. -/
theorem generator_energy {P c : ℝ} (hP : P ≠ 0)
    (w : C(UnitAddTorus ι, ℝ)) (dw : ι → C(UnitAddTorus ι, ℝ))
    (hd : ∀ i (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => w (x + Pi.single i (s : UnitAddCircle)))
        (P * dw i (x + Pi.single i (t : UnitAddCircle))) t)
    (hbound : ∀ x, (∑ i, (dw i x) ^ 2) ≤ c * (w x) ^ 2)
    (u g : RealState ι)
    (hg : HasDerivWithinAt (fun t : ℝ => realHeat P t u) g (Ici 0) 0) :
    inner ℝ (weight w g) (weight w u) ≤ c * ‖weight w u‖ ^ 2 := by
  have hgen := (HeatTorusFourier.generator_iff_coefficients P _ _).mpr
    ((HeatTorusSubeigen.generator_iff_coefficients P u g).mp hg)
  obtain ⟨D, hD⟩ := exists_gradient_of_generator P (embed u) (embed g) hgen
  let w₂ := w * w
  let dw₂ (i : ι) : C(UnitAddTorus ι, ℝ) :=
    ⟨fun x => 2 * w x * dw i x, (continuous_const.mul w.continuous).mul (dw i).continuous⟩
  have hd₂ (i : ι) (x : UnitAddTorus ι) (t : ℝ) :
      HasDerivAt (fun s : ℝ => w₂ (x + Pi.single i (s : UnitAddCircle)))
        (P * dw₂ i (x + Pi.single i (t : UnitAddCircle))) t := by
    convert (hd i x t).mul (hd i x t) using 1
    change P * (2 * w (x + Pi.single i (t : UnitAddCircle)) *
      dw i (x + Pi.single i (t : UnitAddCircle))) = _
    ring
  let Q (i : ι) := fullMultiplier (asComplex (dw₂ i)) (embed u) +
    fullMultiplier (asComplex w₂) (D i)
  have hQ : HasGradient P (embed (weight w₂ u)) Q := by
    rw [embed_weight]
    apply HeatTorusGradientProduct.product hP (asComplex w₂) (fun i => asComplex (dw₂ i)) _ _ _ hD
    intro i x t
    change HasDerivAt (fun s : ℝ => ((w₂ (x + Pi.single i (s : UnitAddCircle)) : ℝ) : ℂ))
      ((P : ℂ) * (dw₂ i (x + Pi.single i (t : UnitAddCircle)) : ℂ)) t
    rw [← Complex.ofReal_mul]
    exact (hd₂ i x t).ofReal_comp
  rw [inner_weight, real_generator_inner_eq_gradient P u g (weight w₂ u) D Q hg hD hQ,
    ← Finset.sum_neg_distrib]
  have hc (i : ι) : -(inner ℂ (D i) (Q i)).re ≤ ∫ x, (dw i x * u x) ^ 2 := by
    have hi := L2.integrable_inner (𝕜 := ℂ) (D i) (Q i)
    have he := Complex.reCLM.integral_comp_comm hi
    change (∫ x, (inner ℂ (D i x) (Q i x)).re) = (∫ x, inner ℂ (D i x) (Q i x)).re at he
    rw [L2.inner_def, ← he, ← integral_neg]
    apply integral_mono_ae hi.re.neg (integrable_square (dw i) u)
    filter_upwards [Lp.coeFn_add (fullMultiplier (asComplex (dw₂ i)) (embed u))
      (fullMultiplier (asComplex w₂) (D i)), fullMultiplier_ae (asComplex (dw₂ i)) (embed u),
      fullMultiplier_ae (asComplex w₂) (D i), embed_ae u] with x h₁ h₂ h₃ h₄
    change -(inner ℂ (D i x) (Q i x)).re ≤ _
    rw [show Q i x = _ from h₁, Pi.add_apply, h₂, h₃, h₄]
    change -(inner ℂ (D i x) (((2 * w x * dw i x : ℝ) : ℂ) * (u x : ℂ) +
      ((w x * w x : ℝ) : ℂ) * D i x)).re ≤ (dw i x * u x) ^ 2
    simpa only [Complex.normSq_ofReal, ← pow_two, mul_pow]
      using coordinate_energy (w x) (dw i x) (u x : ℂ) (D i x)
  refine (Finset.sum_le_sum fun i _ => hc i).trans ?_
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_square (dw i) u), integrated_square,
    ← integral_const_mul]
  apply integral_mono_ae (integrable_finsetSum _ (fun i _ => integrable_square (dw i) u))
    ((integrable_square w u).const_mul c)
  apply Eventually.of_forall
  intro x
  simp_rw [mul_pow, ← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right (hbound x) (sq_nonneg (u x))).trans_eq (by ring)

/-- The exact smooth weighted estimate on the real Fourier heat semigroup. -/
theorem heat_bound {P c : ℝ} (hP : P ≠ 0)
    (w : C(UnitAddTorus ι, ℝ)) (dw : ι → C(UnitAddTorus ι, ℝ))
    (hd : ∀ i (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => w (x + Pi.single i (s : UnitAddCircle)))
        (P * dw i (x + Pi.single i (t : UnitAddCircle))) t)
    (hbound : ∀ x, (∑ i, (dw i x) ^ 2) ≤ c * (w x) ^ 2)
    (T : ℝ≥0) (f : RealState ι) :
    ‖weight w (realHeat P T f)‖ ≤ Real.exp ((T : ℝ) * c) * ‖weight w f‖ :=
  HeatTorusWeightedEuler.heat_bound P c (weight w) (generator_energy hP w dw hd hbound) T f

end HeatTorusSmoothWeight

#print axioms HeatTorusSmoothWeight.generator_energy
#print axioms HeatTorusSmoothWeight.heat_bound
