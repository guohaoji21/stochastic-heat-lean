import HeatTorusReal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Convex.Integral

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatTorusGaussian

open MeasureTheory ProbabilityTheory UnitAddTorus HeatTorusFourier HeatTorusReal Filter
open scoped ENNReal NNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (AddCircle.haarAddCircle (T := 1)).IsAddHaarMeasure
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

/-- Variance in the unit-torus coordinates for physical period `P`. -/
def variance (P t : ℝ) : ℝ≥0 := (2 * max t 0 / P^2).toNNReal

def wrap (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

theorem continuous_wrap : Continuous (wrap (ι := ι)) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

/-- Law of the Gaussian increment, reduced modulo the unit periods. -/
def increment (P t : ℝ) : Measure (UnitAddTorus ι) :=
  (Measure.pi (fun _ : ι => gaussianReal 0 (variance P t))).map wrap

instance (P t : ℝ) : IsProbabilityMeasure (increment (ι := ι) P t) where
  measure_univ := by
    rw [increment, Measure.map_apply continuous_wrap.measurable MeasurableSet.univ,
      Set.preimage_univ, measure_univ]

private theorem one_dimensional_character (P t : ℝ) (k : ℤ) :
    (∫ x : ℝ, fourier k (x : UnitAddCircle) ∂gaussianReal 0 (variance P t)) =
      (Real.exp (-max t 0 * ((2 * Real.pi / P)^2 * (k : ℝ)^2)) : ℂ) := by
  have hf (x : ℝ) : fourier k (x : UnitAddCircle) =
      Complex.exp ((↑(2 * Real.pi * (k : ℝ)) : ℂ) * x * Complex.I) := by
    rw [fourier_coe_apply]
    push_cast
    simp only [div_one]
    congr 1
    ring
  have hv : (variance P t : ℝ) = 2 * max t 0 / P^2 :=
    Real.coe_toNNReal _ (div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) (sq_nonneg _))
  simp_rw [hf]
  rw [← charFun_apply_real, charFun_gaussianReal, Complex.ofReal_exp]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  congr 1
  have hv' : (variance P t : ℂ) = ((2 * max t 0 / P^2 : ℝ) : ℂ) :=
    congrArg (fun x : ℝ => (x : ℂ)) hv
  rw [hv']
  push_cast
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

theorem integral_character (P t : ℝ) (k : ι → ℤ) :
    (∫ z, mFourier k z ∂increment P t) = multiplier P t k := by
  rw [increment, integral_map continuous_wrap.measurable.aemeasurable
    (mFourier k).continuous.aestronglyMeasurable]
  change (∫ x : ι → ℝ, ∏ i, fourier (k i) (x i : UnitAddCircle)
    ∂Measure.pi (fun _ : ι => gaussianReal 0 (variance P t))) = _
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => fourier (k i) (x : UnitAddCircle))]
  simp_rw [one_dimensional_character, ← Complex.ofReal_prod, ← Real.exp_sum]
  unfold multiplier frequencySquared
  congr 2
  rw [← Finset.mul_sum, ← Finset.mul_sum]

def translation (z : UnitAddTorus ι) : C(UnitAddTorus ι, UnitAddTorus ι) :=
  ⟨fun x => x + z, continuous_id.add continuous_const⟩

theorem translation_preserving (z : UnitAddTorus ι) :
    MeasurePreserving (translation z) volume volume := measurePreserving_add_right volume z

def shift {E : Type*} [NormedAddCommGroup E] (f : Lp E 2 (volume : Measure (UnitAddTorus ι)))
    (z : UnitAddTorus ι) : Lp E 2 (volume : Measure (UnitAddTorus ι)) :=
  Lp.compMeasurePreserving (translation z) (translation_preserving z) f

theorem shift_ae {E : Type*} [NormedAddCommGroup E] (f : Lp E 2 (volume : Measure (UnitAddTorus ι)))
    (z : UnitAddTorus ι) : (shift f z : UnitAddTorus ι → E) =ᵐ[volume] fun x => f (x + z) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem shift_norm {E : Type*} [NormedAddCommGroup E] (f : Lp E 2 (volume : Measure (UnitAddTorus ι)))
    (z : UnitAddTorus ι) : ‖shift f z‖ = ‖f‖ := Lp.norm_compMeasurePreserving _ _

theorem continuous_shift {E : Type*} [NormedAddCommGroup E] (f : Lp E 2 (volume : Measure (UnitAddTorus ι))) :
    Continuous (shift f) := by
  have hc : Continuous (translation (ι := ι)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : UnitAddTorus ι × UnitAddTorus ι => p.2 + p.1)
    fun_prop
  exact continuous_const.compMeasurePreservingLp hc translation_preserving (by norm_num)

theorem integrable_shift {E : Type*} [NormedAddCommGroup E] (P t : ℝ)
    (f : Lp E 2 (volume : Measure (UnitAddTorus ι))) : Integrable (shift f) (increment P t) := by
  apply Integrable.of_bound (continuous_shift f).aestronglyMeasurable (‖f‖)
  exact Filter.Eventually.of_forall fun z => (shift_norm f z).le

private theorem character_add_points (k : ι → ℤ) (x z : UnitAddTorus ι) :
    mFourier k (x + z) = mFourier k x * mFourier k z := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem fourierCoeff_shift (f : State ι) (z : UnitAddTorus ι) (k : ι → ℤ) :
    mFourierCoeff (shift f z) k = mFourier k z * mFourierCoeff f k := by
  have hc : mFourier (-k) z * mFourier k z = 1 := by
    rw [← mFourier_add, neg_add_cancel, mFourier_zero]
    rfl
  unfold mFourierCoeff
  simp only [smul_eq_mul]
  calc
    _ = ∫ x : UnitAddTorus ι, mFourier k z * (mFourier (-k) (x+z) * f (x+z)) := by
      apply integral_congr_ae
      filter_upwards [shift_ae f z] with x hx
      rw [hx, character_add_points]
      linear_combination -hc * (mFourier (-k) x * f (x+z))
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact integral_add_right_eq_self (fun x : UnitAddTorus ι => mFourier (-k) x * f x) z

/-- The Fourier heat operator is the Bochner average of translations by
the wrapped Gaussian increment. -/
theorem heat_eq_integral_shift (P t : ℝ) (f : State ι) :
    heat P t f = ∫ z, shift f z ∂increment P t := by
  apply (mFourierBasis (d := ι)).repr.injective
  apply lp.ext
  funext k
  rw [mFourierBasis_repr, mFourierBasis_repr, ← coefficientCLM_apply, ← coefficientCLM_apply,
    ← (coefficientCLM k).integral_comp_comm (integrable_shift P t f)]
  simp only [coefficientCLM_apply, fourierCoeff_heat, fourierCoeff_shift]
  rw [integral_mul_const, integral_character]

theorem embed_shift (f : RealState ι) (z : UnitAddTorus ι) :
    embed (shift f z) = shift (embed f) z := by
  apply Lp.ext
  filter_upwards [embed_ae (shift f z), shift_ae (embed f) z, shift_ae f z,
    (translation_preserving z).quasiMeasurePreserving.ae (embed_ae f)] with x he hs hf hx
  rw [he, hs, hf]
  exact hx.symm

theorem realHeat_eq_integral_shift (P t : ℝ) (f : RealState ι) :
    realHeat P t f = ∫ z, shift f z ∂increment P t := by
  have he : embed (realHeat P t f) = embed (∫ z, shift f z ∂increment P t) := by
    rw [embed_realHeat, heat_eq_integral_shift, ← embed.integral_comp_comm (integrable_shift P t f)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (embed_shift f z).symm
  simpa only [realPart_embed] using congrArg (HeatTorusReal.realPart (ι := ι)) he

private def nonnegative (ι : Type*) [Fintype ι] : Set (RealState ι) :=
  {f | ∀ᵐ x ∂volume, 0 ≤ f x}

private theorem nonnegative_closed : IsClosed (nonnegative ι) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u f hu ht
  obtain ⟨σ, _, hσ⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  filter_upwards [hσ, ae_all_iff.mpr hu] with x hx hn
  exact ge_of_tendsto hx (Eventually.of_forall (fun n => hn (σ n)))

private theorem nonnegative_convex : Convex ℝ (nonnegative ι) := by
  intro f hf g hg a b ha hb _
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
    with x hfx hgx hadd hfa hgb
  rw [hadd]
  change 0 ≤ (a • f) x + (b • g) x
  rw [hfa, hgb]
  exact add_nonneg (mul_nonneg ha hfx) (mul_nonneg hb hgx)

theorem integral_nonnegative {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → RealState ι) (hF : Integrable F μ)
    (hpos : ∀ᵐ s ∂μ, ∀ᵐ x ∂volume, 0 ≤ F s x) :
    ∀ᵐ x ∂volume, 0 ≤ (∫ s, F s ∂μ) x := by
  by_cases hμ : μ = 0
  · rw [hμ, integral_zero_measure]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
      (μ := (volume : Measure (UnitAddTorus ι)))] with x hx
    rw [hx]
    exact le_rfl
  letI : NeZero μ := ⟨hμ⟩
  have ha : ∀ᵐ x ∂volume, 0 ≤ (⨍ s, F s ∂μ) x :=
    Convex.average_mem nonnegative_convex nonnegative_closed hpos hF
  rw [← measure_smul_average]
  filter_upwards [ha, Lp.coeFn_smul (μ.real Set.univ) (⨍ s, F s ∂μ)] with x hx hs
  rw [hs]
  exact mul_nonneg measureReal_nonneg hx

theorem realHeat_nonnegative (P t : ℝ) (f : RealState ι)
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x) : ∀ᵐ x ∂volume, 0 ≤ realHeat P t f x := by
  rw [realHeat_eq_integral_shift]
  apply Convex.integral_mem nonnegative_convex nonnegative_closed _ (integrable_shift P t f)
  apply Filter.Eventually.of_forall
  intro z
  change ∀ᵐ x ∂volume, 0 ≤ shift f z x
  filter_upwards [shift_ae f z, (translation_preserving z).quasiMeasurePreserving.ae hf] with x hx hfx
  rw [hx]
  exact hfx

end HeatTorusGaussian

#print axioms HeatTorusGaussian.integral_character
#print axioms HeatTorusGaussian.heat_eq_integral_shift
#print axioms HeatTorusGaussian.realHeat_eq_integral_shift
#print axioms HeatTorusGaussian.realHeat_nonnegative
