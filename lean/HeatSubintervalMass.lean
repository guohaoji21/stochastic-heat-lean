import HeatL2Order
import HeatPaperPositivity
import HeatRestrictionAdjoint

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace HeatSubintervalMass

open MeasureTheory Filter Set
open HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal BigOperators

def plateau : Set ℝ := Ioo (25 / 4) (27 / 4)

abbrev SubintervalState := Lp ℝ 2 (baseMeasure.restrict plateau)

abbrev restrict : Base →L[ℝ] SubintervalState :=
  HeatRestrictionAdjoint.restriction baseMeasure plateau

abbrev extend : SubintervalState →L[ℝ] Base :=
  HeatRestrictionAdjoint.adjointExtension baseMeasure plateau

private theorem measurable_plateau : MeasurableSet plateau := measurableSet_Ioo

theorem restrict_extend (f : SubintervalState) : restrict (extend f) = f := by
  apply Lp.ext
  filter_upwards [HeatRestrictionAdjoint.restriction_ae baseMeasure plateau (extend f),
    ae_restrict_of_ae (HeatRestrictionAdjoint.adjointExtension_ae baseMeasure plateau
      measurable_plateau f), ae_restrict_mem measurable_plateau] with x hr he hx
  rw [hr, he, indicator_of_mem hx]

theorem extend_restrict_of_support (f : Base)
    (hf : ∀ᵐ x ∂baseMeasure, x ∉ plateau → f x = 0) : extend (restrict f) = f := by
  apply Lp.ext
  have hr := (ae_restrict_iff' measurable_plateau).mp
    (HeatRestrictionAdjoint.restriction_ae baseMeasure plateau f)
  filter_upwards [HeatRestrictionAdjoint.adjointExtension_ae baseMeasure plateau
    measurable_plateau (restrict f), hr, hf] with x he hr hx
  by_cases hmem : x ∈ plateau
  · rw [he, indicator_of_mem hmem, hr hmem]
  · rw [he, indicator_of_notMem hmem, hx hmem]

theorem extend_nonnegative (f : SubintervalState)
    (hf : ∀ᵐ x ∂baseMeasure.restrict plateau, 0 ≤ f x) :
    ∀ᵐ x ∂baseMeasure, 0 ≤ extend f x := by
  filter_upwards [HeatRestrictionAdjoint.adjointExtension_ae baseMeasure plateau
    measurable_plateau f, (ae_restrict_iff' measurable_plateau).mp hf] with x he hx
  rw [he]
  by_cases h : x ∈ plateau
  · rw [indicator_of_mem h]
    exact hx h
  · rw [indicator_of_notMem h]

private theorem noise_extend (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (hbone : ∀ x ∈ plateau, b x = 1)
    (f : SubintervalState) : noise b hb hbound (extend f) = extend f := by
  apply Lp.ext
  filter_upwards [SHEStochastic.BoundedFieldOperator.operator_ae
    (HeatScalarMultiplier.field baseMeasure b hb hbound) (extend f),
    HeatRestrictionAdjoint.adjointExtension_ae baseMeasure plateau measurable_plateau f]
    with x hm hx
  change noise b hb hbound (extend f) x = b x * extend f x at hm
  rw [hm, hx]
  by_cases hmem : x ∈ plateau
  · rw [hbone x hmem, one_mul]
  · rw [indicator_of_notMem hmem, mul_zero]

variable (smallHeat : ℝ≥0 → SubintervalState →L[ℝ] SubintervalState)
  (hsmall_pos : ∀ t (f : SubintervalState),
    (∀ᵐ x ∂baseMeasure.restrict plateau, 0 ≤ f x) →
      ∀ᵐ x ∂baseMeasure.restrict plateau, 0 ≤ smallHeat t f x)
  (hsmall_add : ∀ s t, smallHeat (s + t) = (smallHeat s).comp (smallHeat t))
  (hdom : ∀ t (f : Base), (∀ᵐ x ∂baseMeasure, 0 ≤ f x) →
    ∀ᵐ x ∂baseMeasure, extend (smallHeat t (restrict f)) x ≤ family t f x)
  (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
  (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (hbpos : ∀ᵐ x ∂baseMeasure, 0 ≤ b x)
  (hbone : ∀ x ∈ plateau, b x = 1)

include hsmall_add in
private theorem smallHeat_apply_add (s t : ℝ≥0) (v : SubintervalState) :
    smallHeat (s + t) v = smallHeat s (smallHeat t v) :=
  DFunLike.congr_fun (hsmall_add s t) v

include hsmall_pos hsmall_add hdom hbpos hbone in
/-- Domain domination for the heat flow implies the corresponding domination
for the paper's averaged covariance operator. -/
theorem covariance_dominates (r : ℝ≥0) (f : Base) (hf : ∀ᵐ x ∂baseMeasure, 0 ≤ f x) :
    ∀ᵐ x ∂baseMeasure, extend (smallHeat r (restrict f)) x ≤
      HeatPaperCovariance.K b hb hbound r f x := by
  let lower := extend (smallHeat r (restrict f))
  let A := HeatCovarianceOperator.integrand family (noise b hb hbound) r f
  let ν := (volume : Measure ℝ).restrict (Ioc 0 1)
  let _ : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Ioc]⟩
  have hrestrict : ∀ᵐ x ∂baseMeasure.restrict plateau, 0 ≤ restrict f x := by
    filter_upwards [HeatRestrictionAdjoint.restriction_ae baseMeasure plateau f,
      ae_restrict_of_ae hf] with x hxf hx
    rwa [hxf]
  have hA (θ : ℝ) (hθ : θ ∈ Ioc (0 : ℝ) 1) :
      ∀ᵐ x ∂baseMeasure, lower x ≤ A θ x := by
    let a := Real.toNNReal ((1 - θ) * (r : ℝ))
    let c := Real.toNNReal (θ * (r : ℝ))
    have hac : a + c = r := by
      have he : (1 - θ) * (r : ℝ) + θ * (r : ℝ) = (r : ℝ) := by ring
      calc
        a + c = Real.toNNReal ((1 - θ) * (r : ℝ) + θ * (r : ℝ)) :=
          (Real.toNNReal_add (mul_nonneg (sub_nonneg.mpr hθ.2) r.property)
            (mul_nonneg hθ.1.le r.property)).symm
        _ = r := by rw [he, Real.toNNReal_coe]
    let e := extend (smallHeat c (restrict f))
    have he : ∀ᵐ x ∂baseMeasure, 0 ≤ e x :=
      extend_nonnegative _ (hsmall_pos c _ hrestrict)
    have hm := HeatPositiveCone.monotone (noise b hb hbound)
      (HeatPaperPositivity.multiplier_nonnegative b hb hbound hbpos) e _ (hdom c f hf)
    rw [noise_extend b hb hbound hbone] at hm
    have hs := HeatPositiveCone.monotone (family a) (HeatPaperPositivity.heat_nonnegative a)
      e _ hm
    have hsub := hdom a e he
    change (∀ᵐ x ∂baseMeasure, extend (smallHeat a (restrict (extend
      (smallHeat c (restrict f))))) x ≤ family a e x) at hsub
    rw [restrict_extend, ← smallHeat_apply_add smallHeat hsmall_add, hac] at hsub
    filter_upwards [hsub, hs] with x hx hy using hx.trans hy
  have hInt : IntervalIntegrable A volume 0 1 :=
    HeatCovarianceOperator.integrable family family_continuous family_contraction (noise b hb hbound) r f
  have hc : IntervalIntegrable (fun _ : ℝ => lower) volume 0 1 := intervalIntegrable_const
  have hd : Integrable (fun θ => A θ - lower) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hInt.sub hc)
  have hp := HeatPositiveCone.integral_nonnegative ν (fun θ => A θ - lower) hd (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    filter_upwards [hA θ hθ, Lp.coeFn_sub (A θ) lower] with x hx hsub
    rw [hsub]
    exact sub_nonneg.mpr hx)
  have heq : (∫ θ, A θ - lower ∂ν) = HeatPaperCovariance.K b hb hbound r f - lower := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_sub hInt hc, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    rfl
  rw [heq] at hp
  filter_upwards [hp, Lp.coeFn_sub (HeatPaperCovariance.K b hb hbound r f) lower]
    with x hx hsub
  rw [hsub] at hx
  exact sub_nonneg.mp hx

include hsmall_pos hsmall_add hdom hbpos hbone in
/-- For nonuniform cells the comparison uses the sum of the actual lengths. -/
theorem chain_dominates (h : ℕ → ℝ≥0) (N : ℕ) (g : Base)
    (hg : ∀ᵐ x ∂baseMeasure, 0 ≤ g x)
    (hsupp : ∀ᵐ x ∂baseMeasure, x ∉ plateau → g x = 0)
    (hzero : smallHeat 0 = ContinuousLinearMap.id ℝ SubintervalState) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure,
      extend (smallHeat (∑ k ∈ Finset.range n, h (N - k)) (restrict g)) x ≤
        HeatBackwardChain.reverseChain (HeatPaperCovariance.K b hb hbound) h N g n x := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, hzero, ContinuousLinearMap.id_apply,
      extend_restrict_of_support g hsupp, HeatBackwardChain.reverseChain]
    exact Eventually.of_forall fun _ => le_rfl
  | succ n ih =>
    let a := ∑ k ∈ Finset.range n, h (N - k)
    let e := extend (smallHeat a (restrict g))
    have hrg : ∀ᵐ x ∂baseMeasure.restrict plateau, 0 ≤ restrict g x := by
      filter_upwards [HeatRestrictionAdjoint.restriction_ae baseMeasure plateau g,
        ae_restrict_of_ae hg] with x hxf hx
      rwa [hxf]
    have he : ∀ᵐ x ∂baseMeasure, 0 ≤ e x :=
      extend_nonnegative _ (hsmall_pos a _ hrg)
    have hmono := HeatPaperPositivity.K_monotone b hb hbound hbpos (h (N - n)) _ _ ih
    have hlower := covariance_dominates smallHeat hsmall_pos hsmall_add hdom
      b hb hbound hbpos hbone (h (N - n)) e he
    change (∀ᵐ x ∂baseMeasure, extend (smallHeat (h (N - n)) (restrict
      (extend (smallHeat a (restrict g))))) x ≤ HeatPaperCovariance.K b hb hbound
      (h (N - n)) e x) at hlower
    rw [restrict_extend, ← smallHeat_apply_add smallHeat hsmall_add,
      add_comm (h (N - n))] at hlower
    rw [HeatBackwardChain.reverseChain, Finset.sum_range_succ]
    filter_upwards [hlower, hmono] with x hx hm using hx.trans hm

include hsmall_pos hsmall_add hdom hbpos hbone in
/-- The exact expression on the right of the paper's mass bound follows
from the smaller semigroup comparison and self-adjointness. -/
theorem initial_pairing_bound (h : ℕ → ℝ≥0) (N : ℕ) (g : Base)
    (hg : ∀ᵐ x ∂baseMeasure, 0 ≤ g x)
    (hsupp : ∀ᵐ x ∂baseMeasure, x ∉ plateau → g x = 0)
    (hzero : smallHeat 0 = ContinuousLinearMap.id ℝ SubintervalState)
    (hsymmetric : ∀ t x y, inner ℝ (smallHeat t x) y = inner ℝ x (smallHeat t y))
    (T : ℝ≥0) (hT : ∑ k ∈ Finset.range N, h (N - k) = T) :
    ‖smallHeat (T / 2) (restrict g)‖ ^ 2 ≤
      inner ℝ g (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g 0) := by
  have hcomp := chain_dominates smallHeat hsmall_pos hsmall_add hdom b hb hbound hbpos hbone
    h N g hg hsupp hzero N
  rw [hT] at hcomp
  have hpair := HeatL2Order.inner_mono g _ _ hg hcomp
  rw [← HeatRestrictionAdjoint.restriction_adjoint_pairing] at hpair
  have hhalf : T / 2 + T / 2 = T := by ring
  have heq : inner ℝ (restrict g) (smallHeat T (restrict g)) =
      ‖smallHeat (T / 2) (restrict g)‖ ^ 2 := by
    calc
      _ = inner ℝ (restrict g) (smallHeat (T / 2) (smallHeat (T / 2) (restrict g))) := by
        rw [← smallHeat_apply_add smallHeat hsmall_add, hhalf]
      _ = _ := by rw [← hsymmetric, real_inner_self_eq_norm_sq]
  rw [heq] at hpair
  simpa only [HeatBackwardChain.stateAt, Nat.sub_zero] using hpair

theorem subinterval_heat_energy_positive (t : ℝ≥0)
    (hinj : Function.Injective (smallHeat t)) (g : Base) (hgne : g ≠ 0)
    (hsupp : ∀ᵐ x ∂baseMeasure, x ∉ plateau → g x = 0) :
    0 < ‖smallHeat t (restrict g)‖ ^ 2 := by
  have hr : restrict g ≠ 0 := by
    intro hz
    have he := extend_restrict_of_support g hsupp
    rw [hz, map_zero] at he
    exact hgne he.symm
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hr
  apply hinj
  rw [hz, map_zero]

end HeatSubintervalMass

#print axioms HeatSubintervalMass.covariance_dominates
#print axioms HeatSubintervalMass.initial_pairing_bound
#print axioms HeatSubintervalMass.subinterval_heat_energy_positive
