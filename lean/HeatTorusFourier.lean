import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatTorusFourier

open MeasureTheory UnitAddTorus
open scoped ENNReal ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*}

abbrev State (ι : Type*) [Fintype ι] :=
  Lp ℂ 2 (volume : Measure (UnitAddTorus ι))

abbrev Coefficients (ι : Type*) := lp (fun _ : ι → ℤ => ℂ) 2

variable [Fintype ι]

/-- Squared frequency for the period-`P` torus in unit coordinates. -/
def frequencySquared (P : ℝ) (k : ι → ℤ) : ℝ :=
  (2 * Real.pi / P) ^ 2 * ∑ i, (k i : ℝ) ^ 2

theorem frequencySquared_nonneg (P : ℝ) (k : ι → ℤ) : 0 ≤ frequencySquared P k := by
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg (k i : ℝ))

theorem frequencySquared_two_pi (k : ι → ℤ) :
    frequencySquared (2 * Real.pi) k = ∑ i, (k i : ℝ) ^ 2 := by
  have h : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  simp [frequencySquared, h]

def multiplier (P t : ℝ) (k : ι → ℤ) : ℂ :=
  (Real.exp (-max t 0 * frequencySquared P k) : ℂ)

theorem multiplier_norm_le (P t : ℝ) (k : ι → ℤ) : ‖multiplier P t k‖ ≤ 1 := by
  rw [multiplier, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _))
      (frequencySquared_nonneg P k))

private def scalarMap (P t : ℝ) (k : ι → ℤ) : ℂ →L[ℂ] ℂ :=
  multiplier P t k • ContinuousLinearMap.id ℂ ℂ

private theorem scalarMap_norm_le (P t : ℝ) (k : ι → ℤ) : ‖scalarMap P t k‖ ≤ 1 := by
  simpa [scalarMap, norm_smul] using multiplier_norm_le P t k

private def diagonal (P t : ℝ) : Coefficients ι →L[ℂ] Coefficients ι :=
  lp.mapCLM 2 (scalarMap P t) zero_le_one (scalarMap_norm_le P t)

/-- Fourier heat evolution for the period-`P` scaling. Negative times are clamped to zero. -/
def heat (P t : ℝ) : State ι →L[ℂ] State ι :=
  let basis := mFourierBasis (d := ι)
  basis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    diagonal P t ∘L
    basis.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem fourierCoeff_heat (P t : ℝ) (f : State ι) (k : ι → ℤ) :
    mFourierCoeff (heat P t f) k = multiplier P t k * mFourierCoeff f k := by
  rw [← mFourierBasis_repr (heat P t f) k]
  change (mFourierBasis (d := ι)).repr ((mFourierBasis (d := ι)).repr.symm _) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change multiplier P t k * mFourierBasis.repr f k = _
  rw [mFourierBasis_repr]

theorem contraction (P t : ℝ) (f : State ι) : ‖heat P t f‖ ≤ ‖f‖ := by
  change ‖mFourierBasis.repr.symm (diagonal P t (mFourierBasis.repr f))‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  have h := (diagonal (ι := ι) P t).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 (scalarMap P t) zero_le_one (scalarMap_norm_le P t))
    (mFourierBasis.repr f)
  simpa using h

theorem heat_zero (P : ℝ) : heat P 0 = ContinuousLinearMap.id ℂ (State ι) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (mFourierBasis (d := ι)).repr.injective
  apply lp.ext
  funext k
  simp [mFourierBasis_repr, fourierCoeff_heat, multiplier]

theorem heat_add (P : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heat (ι := ι) P (s + t) = (heat P s).comp (heat P t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (mFourierBasis (d := ι)).repr.injective
  apply lp.ext
  funext k
  simp only [mFourierBasis_repr, ContinuousLinearMap.comp_apply, fourierCoeff_heat,
    multiplier, max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht)]
  rw [show -(s + t) * frequencySquared P k =
    -s * frequencySquared P k + -t * frequencySquared P k by ring,
    Real.exp_add, Complex.ofReal_mul, mul_assoc]

theorem heat_injective (P t : ℝ) : Function.Injective (heat (ι := ι) P t) := by
  intro f g hfg
  apply (mFourierBasis (d := ι)).repr.injective
  apply lp.ext
  funext k
  have h := congrArg (fun u : State ι => mFourierCoeff u k) hfg
  rw [fourierCoeff_heat, fourierCoeff_heat] at h
  simpa only [mFourierBasis_repr] using mul_left_cancel₀
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne' : multiplier P t k ≠ 0) h

theorem heat_symmetric (P t : ℝ) (f g : State ι) :
    inner ℂ (heat P t f) g = inner ℂ f (heat P t g) := by
  let basis := mFourierBasis (d := ι)
  calc
    _ = inner ℂ (basis.repr (heat P t f)) (basis.repr g) :=
      (basis.repr.inner_map_map _ _).symm
    _ = inner ℂ (basis.repr f) (basis.repr (heat P t g)) := by
      rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
      apply tsum_congr
      intro k
      simp only [basis, mFourierBasis_repr, fourierCoeff_heat, RCLike.inner_apply,
        map_mul, multiplier, Complex.conj_ofReal]
      ring
    _ = _ := basis.repr.inner_map_map _ _

theorem continuous_heat (P : ℝ) (f : State ι) : Continuous (fun t : ℝ => heat P t f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have hc (k : ι → ℤ) : Continuous (fun t : ℝ =>
      ‖(multiplier P t k - multiplier P s k) * mFourierCoeff f k‖ ^ 2) := by
    unfold multiplier
    fun_prop
  have hb (k : ι → ℤ) (t : ℝ) :
      ‖‖(multiplier P t k - multiplier P s k) * mFourierCoeff f k‖ ^ 2‖ ≤
        4 * ‖mFourierCoeff f k‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have hw : ‖multiplier P t k - multiplier P s k‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [multiplier_norm_le P t k, multiplier_norm_le P s k])
    have hsq : ‖multiplier P t k - multiplier P s k‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (multiplier P t k - multiplier P s k)]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hseries := continuous_tsum hc ((hasSum_sq_mFourierCoeff f).summable.mul_left 4) hb
  have hsquare (g : State ι) : ‖g‖ ^ 2 = ∑' k : ι → ℤ, ‖mFourierCoeff g k‖ ^ 2 := by
    rw [← (mFourierBasis (d := ι)).repr.norm_map g]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mFourierBasis_repr] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (mFourierBasis.repr g))
  have hn : Continuous (fun t : ℝ => ‖heat P t f - heat P s f‖ ^ 2) := by
    convert hseries using 1
    funext t
    rw [hsquare]
    apply tsum_congr
    intro k
    rw [← mFourierBasis_repr (heat P t f - heat P s f) k, map_sub]
    change ‖mFourierBasis.repr (heat P t f) k - mFourierBasis.repr (heat P s f) k‖ ^ 2 = _
    rw [mFourierBasis_repr, mFourierBasis_repr, fourierCoeff_heat, fourierCoeff_heat, sub_mul]
  have hl : Filter.Tendsto (fun t : ℝ => ‖heat P t f - heat P s f‖) (nhds s) (nhds 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Real.sqrt_zero,
      Real.sqrt_sq (norm_nonneg _)] using (hn.tendsto s).sqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hl

def coefficientCLM (k : ι → ℤ) : State ι →L[ℝ] ℂ :=
  (lp.evalCLM ℝ (fun _ : ι → ℤ => ℂ) 2 k).comp
    ((mFourierBasis (d := ι)).repr.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

theorem coefficientCLM_apply (k : ι → ℤ) (f : State ι) :
    coefficientCLM k f = mFourierCoeff f k := mFourierBasis_repr f k

private theorem exp_hasDerivAt (c t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => (Real.exp (-s * c) : ℂ) * z)
      ((Real.exp (-t * c) : ℂ) * ((↑(-c) : ℂ) * z)) t := by
  have h := (Real.hasDerivAt_exp (-t * c)).comp t (((hasDerivAt_id t).neg).mul_const c)
  have hr : HasDerivAt (fun s : ℝ => Real.exp (-s * c)) (Real.exp (-t * c) * -c) t := by
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, neg_mul, one_mul] using h
  simpa only [Complex.ofReal_mul, mul_assoc] using hr.ofReal_comp.mul_const z

theorem orbit_integral (P : ℝ) (f g : State ι)
    (hfg : ∀ k, mFourierCoeff g k = (↑(-frequencySquared P k) : ℂ) * mFourierCoeff f k)
    (t : ℝ) (ht : 0 ≤ t) :
    heat P t f - f = ∫ s in (0 : ℝ)..t, heat P s g := by
  apply (mFourierBasis (d := ι)).repr.injective
  apply lp.ext
  funext k
  rw [mFourierBasis_repr, mFourierBasis_repr, ← coefficientCLM_apply, ← coefficientCLM_apply,
    map_sub, ← (coefficientCLM k).intervalIntegral_comp_comm
      ((continuous_heat P g).intervalIntegrable 0 t)]
  simp only [coefficientCLM_apply, fourierCoeff_heat, multiplier, max_eq_left ht]
  let c := frequencySquared P k
  have hd (s : ℝ) : HasDerivAt (fun u : ℝ => (Real.exp (-u*c) : ℂ) * mFourierCoeff f k)
      ((Real.exp (-s*c) : ℂ) * mFourierCoeff g k) s := by
    rw [hfg k]
    exact exp_hasDerivAt c s (mFourierCoeff f k)
  have hc : Continuous (fun s : ℝ => (Real.exp (-s*c) : ℂ) * mFourierCoeff g k) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 t)
  simp only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro s hs
  change ((Real.exp (-s * c) : ℂ) * mFourierCoeff g k) =
    (Real.exp (-max s 0 * c) : ℂ) * mFourierCoeff g k
  rw [max_eq_left (Set.mem_Icc.mp ((Set.uIcc_of_le ht) ▸ hs)).1]

theorem generator_iff_coefficients (P : ℝ) (f g : State ι) :
    HasDerivWithinAt (fun t : ℝ => heat P t f) g (Set.Ici 0) 0 ↔
      ∀ k, mFourierCoeff g k = (↑(-frequencySquared P k) : ℂ) * mFourierCoeff f k := by
  constructor
  · intro hg k
    have h := (coefficientCLM k).hasFDerivAt.comp_hasDerivWithinAt 0 hg
    have hL : HasDerivWithinAt (fun t : ℝ => mFourierCoeff (heat P t f) k)
        (mFourierCoeff g k) (Set.Ici 0) 0 := by
      simpa only [Function.comp_def, coefficientCLM_apply] using h
    have hR : HasDerivWithinAt (fun t : ℝ => mFourierCoeff (heat P t f) k)
        ((↑(-frequencySquared P k) : ℂ) * mFourierCoeff f k) (Set.Ici 0) 0 := by
      have hd := exp_hasDerivAt (frequencySquared P k) 0 (mFourierCoeff f k)
      simp only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] at hd
      apply hd.hasDerivWithinAt.congr_of_mem _ (Set.mem_Ici.mpr le_rfl)
      intro t ht
      rw [fourierCoeff_heat, multiplier, max_eq_left ht]
    have he := (uniqueDiffWithinAt_Ici 0).eq hL hR
    simpa using congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) he
  · intro hg
    have hc := continuous_heat P g
    have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    rw [heat_zero, ContinuousLinearMap.id_apply] at hd
    apply (hd.add_const f).hasDerivWithinAt.congr_of_mem _ (Set.mem_Ici.mpr le_rfl)
    intro t ht
    exact sub_eq_iff_eq_add.mp (orbit_integral P f g hg t ht)

end HeatTorusFourier

#print axioms HeatTorusFourier.heat_add
#print axioms HeatTorusFourier.continuous_heat
#print axioms HeatTorusFourier.heat_symmetric
#print axioms HeatTorusFourier.generator_iff_coefficients
