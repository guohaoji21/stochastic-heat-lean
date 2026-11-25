import HeatTorusAxisFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatTorusGradient

open MeasureTheory UnitAddTorus HeatTorusFourier
open scoped ENNReal ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

/-- The Fourier symbol of the physical derivative in coordinate `i`. -/
def symbol (P : ℝ) (i : ι) (k : ι → ℤ) : ℂ :=
  (((2 * Real.pi / P) * (k i : ℝ) : ℝ) : ℂ) * Complex.I

/-- An `L²` gradient specified by its Fourier coefficients. -/
def HasGradient (P : ℝ) (u : State ι) (D : ι → State ι) : Prop :=
  ∀ i k, mFourierCoeff (D i) k = symbol P i k * mFourierCoeff u k

omit [Fintype ι] in
private theorem symbol_norm_sq (P : ℝ) (i : ι) (k : ι → ℤ) :
    ‖symbol P i k‖ ^ 2 = (2 * Real.pi / P) ^ 2 * (k i : ℝ) ^ 2 := by
  rw [symbol, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, mul_pow]

private theorem sum_symbol_norm_sq (P : ℝ) (k : ι → ℤ) :
    (∑ i, ‖symbol P i k‖ ^ 2) = frequencySquared P k := by
  simp_rw [symbol_norm_sq, ← Finset.mul_sum, frequencySquared]

private theorem symbol_bound (P : ℝ) (i : ι) (k : ι → ℤ) :
    ‖symbol P i k‖ ≤ 1 + frequencySquared P k := by
  have hsq : ‖symbol P i k‖ ^ 2 ≤ frequencySquared P k := by
    rw [← sum_symbol_norm_sq]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖symbol P i k‖) (Finset.mem_univ i)
  nlinarith only [hsq, sq_nonneg (‖symbol P i k‖ - 1)]

private def normalizedSymbol (P : ℝ) (i : ι) (k : ι → ℤ) : ℂ :=
  symbol P i k / ((1 + frequencySquared P k : ℝ) : ℂ)

private def normalizedMode (P : ℝ) (i : ι) (k : ι → ℤ) : ℂ →L[ℂ] ℂ :=
  normalizedSymbol P i k • ContinuousLinearMap.id ℂ ℂ

private theorem normalizedMode_bound (P : ℝ) (i : ι) (k : ι → ℤ) :
    ‖normalizedMode P i k‖ ≤ 1 := by
  have hc : 0 < 1 + frequencySquared P k :=
    add_pos_of_pos_of_nonneg zero_lt_one (frequencySquared_nonneg P k)
  simpa only [normalizedMode, normalizedSymbol, norm_smul, ContinuousLinearMap.norm_id,
    mul_one, norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, div_le_one hc]
    using symbol_bound P i k

private def normalizedGradient (P : ℝ) (i : ι) : State ι →L[ℂ] State ι :=
  let b := mFourierBasis (d := ι)
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    lp.mapCLM 2 (normalizedMode P i) zero_le_one (normalizedMode_bound P i) ∘L
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap

private theorem coefficient_normalizedGradient (P : ℝ) (i : ι) (f : State ι) (k : ι → ℤ) :
    mFourierCoeff (normalizedGradient P i f) k = normalizedSymbol P i k * mFourierCoeff f k := by
  rw [← mFourierBasis_repr, ← mFourierBasis_repr f k]
  change mFourierBasis.repr (mFourierBasis.repr.symm _) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The Fourier generator domain is contained in the Fourier `H¹` domain. -/
theorem exists_gradient_of_generator (P : ℝ) (u g : State ι)
    (hg : HasDerivWithinAt (fun t : ℝ => heat P t u) g (Set.Ici 0) 0) :
    ∃ D : ι → State ι, HasGradient P u D := by
  refine ⟨fun i => normalizedGradient P i (u - g), ?_⟩
  intro i k
  rw [coefficient_normalizedGradient]
  have hk := (generator_iff_coefficients P u g).mp hg k
  have hsub : mFourierCoeff (u - g) k = mFourierCoeff u k - mFourierCoeff g k := by
    simp only [← coefficientCLM_apply, map_sub]
  rw [normalizedSymbol, hsub, hk]
  have hne : (1 + (frequencySquared P k : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (frequencySquared_nonneg P k)) : 1 + frequencySquared P k ≠ 0)
  push_cast
  field_simp [hne]
  ring

private theorem coefficient_inner (u v : State ι) :
    inner ℂ u v = ∑' k : ι → ℤ, inner ℂ (mFourierCoeff u k) (mFourierCoeff v k) := by
  rw [← (mFourierBasis (d := ι)).repr.inner_map_map u v, lp.inner_eq_tsum]
  simp only [mFourierBasis_repr]

private theorem summable_coefficient_inner (u v : State ι) :
    Summable (fun k : ι → ℤ => inner ℂ (mFourierCoeff u k) (mFourierCoeff v k)) := by
  simpa only [mFourierBasis_repr] using lp.summable_inner
    ((mFourierBasis (d := ι)).repr u) ((mFourierBasis (d := ι)).repr v)

private theorem inner_symbol (z a b : ℂ) :
    inner ℂ (z * a) (z * b) = (↑(‖z‖ ^ 2) : ℂ) * inner ℂ a b := by
  change inner ℂ (z • a) (z • b) = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul, Complex.ofReal_pow]
  rfl

/-- The Fourier heat generator has the spatial gradient form on all
`L²` tests with an `L²` Fourier gradient. -/
theorem generator_inner_eq_gradient (P : ℝ) (u g v : State ι) (Du Dv : ι → State ι)
    (hg : HasDerivWithinAt (fun t : ℝ => heat P t u) g (Set.Ici 0) 0)
    (hu : HasGradient P u Du) (hv : HasGradient P v Dv) :
    inner ℂ g v = -(∑ i, inner ℂ (Du i) (Dv i)) := by
  rw [coefficient_inner g v]
  simp_rw [coefficient_inner (Du _) (Dv _)]
  rw [← Summable.tsum_finsetSum
    (fun i _ => summable_coefficient_inner (Du i) (Dv i)), ← tsum_neg]
  apply tsum_congr
  intro k
  have h := (generator_iff_coefficients P u g).mp hg k
  rw [h]
  have hU i := hu i k
  have hV i := hv i k
  simp_rw [hU, hV, inner_symbol]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_symbol_norm_sq]
  rw [← smul_eq_mul, inner_smul_left, Complex.conj_ofReal, Complex.ofReal_neg, neg_mul]

private theorem coefficient_ae {f g : UnitAddTorus ι → ℂ} (h : f =ᵐ[volume] g) (k : ι → ℤ) :
    mFourierCoeff f k = mFourierCoeff g k := by
  unfold mFourierCoeff
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Continuous coordinate derivatives along the periodic lift give the
same gradient as the Fourier multiplier, with the physical period scaling. -/
theorem hasGradient_of_classical [DecidableEq ι] {P : ℝ} (hP : P ≠ 0)
    (f : UnitAddTorus ι → ℂ) (df : ι → UnitAddTorus ι → ℂ)
    (hf : Continuous f) (hdf : ∀ i, Continuous (df i))
    (hd : ∀ i (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => HeatTorusAxisFourier.sectionAt f i x (s : UnitAddCircle))
        ((P : ℂ) * HeatTorusAxisFourier.sectionAt (df i) i x (t : UnitAddCircle)) t)
    (u : State ι) (D : ι → State ι) (hu : (u : UnitAddTorus ι → ℂ) =ᵐ[volume] f)
    (hD : ∀ i, (D i : UnitAddTorus ι → ℂ) =ᵐ[volume] df i) :
    HasGradient P u D := by
  intro i k
  rw [coefficient_ae hu, coefficient_ae (hD i)]
  have hcoef := HeatTorusAxisFourier.coefficient_derivative f (fun x => (P : ℂ) * df i x)
    hf (continuous_const.mul (hdf i)) i (hd i) k
  have hscale : mFourierCoeff (fun x => (P : ℂ) * df i x) k =
      (P : ℂ) * mFourierCoeff (df i) k := by
    unfold mFourierCoeff
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp only [smul_eq_mul]; ring
  rw [hscale] at hcoef
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hP)
  rw [hcoef]
  unfold symbol
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hP]

/-- The gradient form for the real heat equation, written through its
complex Fourier realization. -/
theorem real_generator_inner_eq_gradient (P : ℝ)
    (u g v : HeatTorusReal.RealState ι) (Du Dv : ι → State ι)
    (hg : HasDerivWithinAt (fun t : ℝ => HeatTorusReal.realHeat P t u) g (Set.Ici 0) 0)
    (hu : HasGradient P (HeatTorusReal.embed u) Du)
    (hv : HasGradient P (HeatTorusReal.embed v) Dv) :
    inner ℝ g v = -(∑ i, (inner ℂ (Du i) (Dv i)).re) := by
  have hgen := (generator_iff_coefficients P _ _).mpr
    ((HeatTorusSubeigen.generator_iff_coefficients P u g).mp hg)
  have h := congrArg Complex.re (generator_inner_eq_gradient P _ _ _ Du Dv hgen hu hv)
  rw [HeatTorusReal.inner_embed_re, Complex.neg_re] at h
  change inner ℝ g v = -(Complex.reCLM (∑ i, inner ℂ (Du i) (Dv i))) at h
  simpa only [map_sum, Complex.reCLM_apply] using h

end HeatTorusGradient

#print axioms HeatTorusGradient.exists_gradient_of_generator
#print axioms HeatTorusGradient.generator_inner_eq_gradient
#print axioms HeatTorusGradient.hasGradient_of_classical
#print axioms HeatTorusGradient.real_generator_inner_eq_gradient
