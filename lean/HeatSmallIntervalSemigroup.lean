import HeatSmallIntervalAffine
import HeatDirichletEuler
import HeatPaperAdjoint

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace HeatSmallIntervalSemigroup

open MeasureTheory Filter HeatIntervalNormalization HeatSmallIntervalAffine HeatSubintervalMass
open scoped ENNReal NNReal Topology

abbrev smallMeasure : Measure ℝ := baseMeasure.restrict plateau

private def scaledMeasure : Measure ℝ := ENNReal.ofReal (1 / 20 : ℝ) • baseMeasure

private theorem unscale_measure : (20 : ℝ≥0∞) • scaledMeasure = baseMeasure := by
  rw [scaledMeasure, smul_smul, show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20)]
  norm_num

private theorem preserve : MeasurePreserving toLarge smallMeasure scaledMeasure :=
  ⟨toLarge.measurable, map_subinterval⟩

private def moveToScaled (f : Base) : Lp ℝ 2 scaledMeasure :=
  ((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).toLp f

private theorem moveToScaled_ae (f : Base) :
    (moveToScaled f : ℝ → ℝ) =ᵐ[scaledMeasure] f :=
  ((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).coeFn_toLp

private def pull (f : Base) : SubintervalState :=
  Lp.compMeasurePreserving toLarge preserve (moveToScaled f)

private theorem pull_ae (f : Base) : (pull f : ℝ → ℝ) =ᵐ[smallMeasure] f ∘ toLarge :=
  (Lp.coeFn_compMeasurePreserving (moveToScaled f) preserve).trans
    (preserve.quasiMeasurePreserving.ae (moveToScaled_ae f))

private def pullLinear : Base →ₗ[ℝ] SubintervalState where
  toFun := pull
  map_add' f g := by
    apply Lp.ext
    have h := preserve.quasiMeasurePreserving.ae
      (Measure.ae_smul_measure (Lp.coeFn_add f g) (ENNReal.ofReal (1 / 20 : ℝ)))
    filter_upwards [pull_ae (f + g), pull_ae f, pull_ae g,
      Lp.coeFn_add (pull f) (pull g), h] with x hfg hf hg hp hh
    simp only [Function.comp_apply, Pi.add_apply] at *
    rw [hfg, hp, hf, hg, hh]
  map_smul' c f := by
    apply Lp.ext
    have h := preserve.quasiMeasurePreserving.ae
      (Measure.ae_smul_measure (Lp.coeFn_smul c f) (ENNReal.ofReal (1 / 20 : ℝ)))
    filter_upwards [pull_ae (c • f), pull_ae f,
      Lp.coeFn_smul c (pull f), h] with x hcf hf hp hh
    simp only [Function.comp_apply, Pi.smul_apply] at *
    change (pull (c • f)) x = (c • pull f) x
    rw [hcf, hp, hf, hh]

private theorem pull_norm_sq (f : Base) : ‖pull f‖ ^ 2 = (1 / 20 : ℝ) * ‖f‖ ^ 2 := by
  rw [realLp_norm_sq, realLp_norm_sq]
  have he : (∫ x, ‖pull f x‖ ^ 2 ∂smallMeasure) = ∫ x, ‖f (toLarge x)‖ ^ 2 ∂smallMeasure := by
    apply integral_congr_ae
    filter_upwards [pull_ae f] with x hx
    rw [hx]
    rfl
  rw [he, preserve.integral_comp' (fun x => ‖f x‖ ^ 2)]
  change (∫ x, ‖f x‖ ^ 2 ∂(ENNReal.ofReal (1 / 20 : ℝ) • baseMeasure)) = _
  rw [integral_smul_measure]
  norm_num

private theorem pull_surjective : Function.Surjective pull := by
  intro g
  let p := Lp.compMeasurePreserving toLarge.symm (preserve.symm toLarge) g
  have hp : MemLp (p : ℝ → ℝ) 2 baseMeasure := by
    have hm := (Lp.memLp p).smul_measure (c := (20 : ℝ≥0∞)) (by norm_num)
    rwa [unscale_measure] at hm
  let f := hp.toLp p
  refine ⟨f, ?_⟩
  apply Lp.ext
  have h := preserve.quasiMeasurePreserving.ae (Measure.ae_smul_measure hp.coeFn_toLp
    (ENNReal.ofReal (1 / 20 : ℝ)))
  have hg := preserve.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving g (preserve.symm toLarge))
  filter_upwards [pull_ae f, h, hg] with x hf he hge
  rw [hf]
  change f (toLarge x) = g x
  rw [he, hge]
  exact congrArg g (toLarge.symm_apply_apply x)

private def scaledPull : Base →ₗᵢ[ℝ] SubintervalState where
  toLinearMap := Real.sqrt 20 • pullLinear
  norm_map' f := by
    change ‖Real.sqrt 20 • pull f‖ = ‖f‖
    have hn : (Real.sqrt 20 * ‖pull f‖) ^ 2 = ‖f‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), pull_norm_sq]
      ring
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp hn

/-- The unnormalized real `L²` spaces are isometric via the affine pullback
multiplied by `sqrt 20`. -/
def transport : Base ≃ₗᵢ[ℝ] SubintervalState :=
  LinearIsometryEquiv.ofSurjective scaledPull (by
    intro g
    obtain ⟨f, hf⟩ := pull_surjective ((Real.sqrt 20)⁻¹ • g)
    refine ⟨f, ?_⟩
    change Real.sqrt 20 • pull f = g
    rw [hf, smul_smul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)), one_smul])

theorem transport_ae (f : Base) : (transport f : ℝ → ℝ) =ᵐ[smallMeasure]
    fun x => Real.sqrt 20 * f (toLarge x) := by
  rw [show transport f = (Real.sqrt 20 : ℝ) • pull f from rfl]
  filter_upwards [Lp.coeFn_smul (Real.sqrt 20) (pull f), pull_ae f] with x hx hf
  rw [hx]
  simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] using congrArg (Real.sqrt 20 * ·) hf

theorem transport_nonnegative_iff (f : Base) :
    (∀ᵐ x ∂smallMeasure, 0 ≤ transport f x) ↔ ∀ᵐ x ∂baseMeasure, 0 ≤ f x := by
  have hp : 0 < Real.sqrt 20 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · intro h
    have hh : ∀ᵐ x ∂smallMeasure, 0 ≤ f (toLarge x) := by
      filter_upwards [h, transport_ae f] with x hx he
      rw [he] at hx
      exact nonneg_of_mul_nonneg_right hx hp
    have he : ∀ᵐ x ∂scaledMeasure, 0 ≤ f x := by
      rw [← preserve.map_eq]
      exact toLarge.measurableEmbedding.ae_map_iff.mpr hh
    simpa only [unscale_measure] using Measure.ae_smul_measure he (20 : ℝ≥0∞)
  · intro h
    filter_upwards [transport_ae f, preserve.quasiMeasurePreserving.ae
      (Measure.ae_smul_measure h (ENNReal.ofReal (1 / 20 : ℝ)))] with x hx hh
    rw [hx]
    exact mul_nonneg hp.le hh

/-- The Dirichlet heat family on the plateau, transported from `(0, 10)`.
The time factor is the square of the spatial dilation. -/
def smallHeat (t : ℝ≥0) : SubintervalState →L[ℝ] SubintervalState :=
  transport.toLinearIsometry.toContinuousLinearMap.comp
    ((paperHeat (400 * (t : ℝ))).comp transport.symm.toLinearIsometry.toContinuousLinearMap)

theorem smallHeat_apply (t : ℝ≥0) (f : SubintervalState) :
    smallHeat t f = transport (paperHeat (400 * (t : ℝ)) (transport.symm f)) := rfl

theorem smallHeat_zero : smallHeat 0 = ContinuousLinearMap.id ℝ SubintervalState := by
  ext f
  simp [smallHeat_apply, paperHeat_zero]

theorem smallHeat_add (s t : ℝ≥0) : smallHeat (s + t) = (smallHeat s).comp (smallHeat t) := by
  ext f
  simp only [smallHeat_apply, NNReal.coe_add, mul_add, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rw [paperHeat_semigroup (by positivity : 0 ≤ 400 * (s : ℝ))
    (by positivity : 0 ≤ 400 * (t : ℝ)), ContinuousLinearMap.comp_apply]

theorem smallHeat_nonnegative (t : ℝ≥0) (f : SubintervalState)
    (hf : ∀ᵐ x ∂smallMeasure, 0 ≤ f x) : ∀ᵐ x ∂smallMeasure, 0 ≤ smallHeat t f x := by
  rw [smallHeat_apply, transport_nonnegative_iff]
  apply HeatDirichletEuler.nonnegative _ (by positivity)
  apply (transport_nonnegative_iff _).mp
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hf

theorem smallHeat_symmetric (t : ℝ≥0) (x y : SubintervalState) :
    inner ℝ (smallHeat t x) y = inner ℝ x (smallHeat t y) := by
  rw [← transport.symm.inner_map_map (smallHeat t x) y,
    ← transport.symm.inner_map_map x (smallHeat t y)]
  simp only [smallHeat_apply, LinearIsometryEquiv.symm_apply_apply]
  exact HeatPaperAdjoint.paper_heat_inner _ _ _

private theorem paperHeat_injective (t : ℝ) (ht : 0 ≤ t) : Function.Injective (paperHeat t) := by
  intro x y h
  have hz : paperHeat t (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hc (k : ℤ) : HeatFourierFrame.coordinate k (x - y) = 0 := by
    have h' := congrArg (HeatFourierFrame.coordinate k) hz
    rw [HeatResolventSpectrum.coordinate_heat t ht, map_zero] at h'
    exact (mul_eq_zero.mp h').resolve_left (Real.exp_pos _).ne'
  have hnorm : ‖x - y‖ ^ 2 = 0 := by
    rw [HeatFourierFrame.parseval]
    simp [hc]
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - y)]))

theorem smallHeat_injective (t : ℝ≥0) : Function.Injective (smallHeat t) := by
  intro x y h
  rw [smallHeat_apply, smallHeat_apply] at h
  exact transport.symm.injective (paperHeat_injective _ (by positivity) (transport.injective h))

theorem euler_tendsto_smallHeat (t : ℝ≥0) (ht : 0 < t) (f : SubintervalState) :
    Tendsto (fun n => transport (HeatDirichletEuler.value (400 * (t : ℝ))
      (by positivity) n (transport.symm f))) atTop (𝓝 (smallHeat t f)) := by
  exact (transport.continuous.tendsto _).comp
    (HeatDirichletEuler.tendsto_heat _ (by positivity) (transport.symm f))

end HeatSmallIntervalSemigroup

#print axioms HeatSmallIntervalSemigroup.transport_ae
#print axioms HeatSmallIntervalSemigroup.smallHeat_add
#print axioms HeatSmallIntervalSemigroup.smallHeat_symmetric
#print axioms HeatSmallIntervalSemigroup.smallHeat_injective
#print axioms HeatSmallIntervalSemigroup.euler_tendsto_smallHeat
