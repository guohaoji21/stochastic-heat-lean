import HeatSmallIntervalSemigroup

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace HeatSmallIntervalEulerOrder

open Filter MeasureTheory Set HeatIntervalNormalization HeatDirichletResolvent
open HeatSmallIntervalSemigroup HeatSubintervalMass HeatEulerScalar
open scoped NNReal Topology

def smallSmoothing (a : ℝ) (ha : 400 ≤ a) : SubintervalState →L[ℝ] SubintervalState :=
  transport.toLinearIsometry.toContinuousLinearMap.comp
    ((smoothing (a / 400) (by linarith)).comp transport.symm.toLinearIsometry.toContinuousLinearMap)

theorem smallSmoothing_apply (a : ℝ) (ha : 400 ≤ a) (f : SubintervalState) :
    smallSmoothing a ha f = transport (smoothing (a / 400) (by linarith) (transport.symm f)) := rfl

private theorem smallSmoothing_nonnegative (a : ℝ) (ha : 400 ≤ a) (f : SubintervalState)
    (hf : ∀ᵐ x ∂smallMeasure, 0 ≤ f x) : ∀ᵐ x ∂smallMeasure, 0 ≤ smallSmoothing a ha f x := by
  rw [smallSmoothing_apply, transport_nonnegative_iff]
  apply HeatResolventSpectrum.smoothing_nonnegative
  apply (transport_nonnegative_iff _).mp
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hf

private theorem extend_restrict_le (f : Base) (hf : ∀ᵐ x ∂baseMeasure, 0 ≤ f x) :
    ∀ᵐ x ∂baseMeasure, extend (restrict f) x ≤ f x := by
  have hr := (ae_restrict_iff' measurableSet_Ioo).mp
    (HeatRestrictionAdjoint.restriction_ae baseMeasure plateau f)
  filter_upwards [HeatRestrictionAdjoint.adjointExtension_ae baseMeasure plateau measurableSet_Ioo
    (restrict f), hr, hf] with x he hh hx
  rw [he]
  by_cases h : x ∈ plateau
  · rw [indicator_of_mem h, hh h]
  · rwa [indicator_of_notMem h]

private theorem restrict_nonnegative (f : Base) (hf : ∀ᵐ x ∂baseMeasure, 0 ≤ f x) :
    ∀ᵐ x ∂smallMeasure, 0 ≤ restrict f x := by
  filter_upwards [HeatRestrictionAdjoint.restriction_ae baseMeasure plateau f,
    ae_restrict_of_ae hf] with x hx h
  rwa [hx]

private theorem iterate_conj (a : ℝ) (ha : 400 ≤ a) (m : ℕ) (f : SubintervalState) :
    ((smallSmoothing a ha : SubintervalState → SubintervalState)^[m]) f =
      transport (((smoothing (a / 400) (by linarith) : Base → Base)^[m]) (transport.symm f)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, smallSmoothing_apply,
      LinearIsometryEquiv.symm_apply_apply]

private theorem iterate_le (a : ℝ) (ha : 400 ≤ a)
    (hcmp : ∀ f : Base, (∀ᵐ x ∂baseMeasure, 0 ≤ f x) →
      ∀ᵐ x ∂baseMeasure, extend (smallSmoothing a ha (restrict f)) x ≤ smoothing a (by linarith) f x)
    (f : Base) (hf : ∀ᵐ x ∂baseMeasure, 0 ≤ f x) (m : ℕ) :
    ∀ᵐ x ∂baseMeasure,
      extend (((smallSmoothing a ha : SubintervalState → SubintervalState)^[m]) (restrict f)) x ≤
      (((smoothing a (by linarith) : Base → Base)^[m]) f) x := by
  have hn (m : ℕ) : ∀ᵐ x ∂smallMeasure,
      0 ≤ (((smallSmoothing a ha : SubintervalState → SubintervalState)^[m]) (restrict f)) x := by
    induction m with
    | zero => exact restrict_nonnegative f hf
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact smallSmoothing_nonnegative a ha _ ih
  induction m with
  | zero => exact extend_restrict_le f hf
  | succ m ih =>
    let Y := ((smallSmoothing a ha : SubintervalState → SubintervalState)^[m]) (restrict f)
    have hstep := hcmp (extend Y) (extend_nonnegative Y (hn m))
    rw [restrict_extend] at hstep
    have hmono := HeatPositiveCone.monotone (smoothing a (by linarith))
      (HeatResolventSpectrum.smoothing_nonnegative (by linarith : 1 ≤ a)) _ _ ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    filter_upwards [hstep, hmono] with x hx hy using hx.trans hy

/-- Domination of the one-step implicit schemes at all sufficiently large
parameters implies domination of the heat semigroups. Both schemes use the
same number of steps, with the spatial scaling accounted for in the clock. -/
theorem heat_domination_of_smoothing
    (hcmp : ∀ (a : ℝ) (ha : 400 ≤ a) (f : Base), (∀ᵐ x ∂baseMeasure, 0 ≤ f x) →
      ∀ᵐ x ∂baseMeasure, extend (smallSmoothing a ha (restrict f)) x ≤ smoothing a (by linarith) f x)
    (t : ℝ≥0) (f : Base) (hf : ∀ᵐ x ∂baseMeasure, 0 ≤ f x) :
    ∀ᵐ x ∂baseMeasure, extend (smallHeat t (restrict f)) x ≤ paperHeat t f x := by
  by_cases ht : t = 0
  · subst t
    simp only [smallHeat_zero, NNReal.coe_zero, paperHeat_zero, ContinuousLinearMap.id_apply]
    exact extend_restrict_le f hf
  have ht' : 0 < (t : ℝ) := by exact_mod_cast (pos_of_ne_zero ht)
  let B := 400 * (t : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  let d := ⌈B⌉₊ - ⌈(t : ℝ)⌉₊
  have hceil : ⌈(t : ℝ)⌉₊ ≤ ⌈B⌉₊ := Nat.ceil_mono (by dsimp [B]; linarith)
  have hcount (n : ℕ) : count (t : ℝ) (n + d) = count B n := by
    dsimp [count, d]
    omega
  have ha (n : ℕ) : 400 ≤ parameter (t : ℝ) (n + d) := by
    apply (le_div_iff₀ ht').2
    rw [hcount]
    exact count_ge B n
  have hpar (n : ℕ) : parameter (t : ℝ) (n + d) / 400 = parameter B n := by
    rw [parameter, parameter, hcount]
    dsimp [B]
    field_simp
  let u := fun n => HeatDirichletEuler.value (t : ℝ) ht' (n + d) f
  let v := fun n => transport (HeatDirichletEuler.value B hB n (transport.symm (restrict f)))
  have hu : Tendsto u atTop (𝓝 (paperHeat t f)) :=
    (HeatDirichletEuler.tendsto_heat _ ht' f).comp (tendsto_add_atTop_nat d)
  have hv : Tendsto v atTop (𝓝 (smallHeat t (restrict f))) :=
    euler_tendsto_smallHeat t (pos_of_ne_zero ht) (restrict f)
  have horder (n : ℕ) : ∀ᵐ x ∂baseMeasure, extend (v n) x ≤ u n x := by
    have he := iterate_le _ (ha n) (hcmp _ (ha n)) f hf (count (t : ℝ) (n + d))
    rw [iterate_conj] at he
    change ∀ᵐ x ∂baseMeasure, _ ≤ HeatDirichletEuler.value (t : ℝ) ht' (n + d) f x at he
    simpa only [hpar, hcount, HeatDirichletEuler.value, v, u] using he
  have hlim := hu.sub ((extend.continuous.tendsto _).comp hv)
  have hp := HeatFourierFrameConvergence.nonnegative_limit _ _ hlim (fun n => by
    filter_upwards [horder n, Lp.coeFn_sub (u n) (extend (v n))] with x hx he
    change 0 ≤ (u n - extend (v n)) x
    rw [he]
    exact sub_nonneg.mpr hx)
  filter_upwards [hp, Lp.coeFn_sub (paperHeat t f) (extend (smallHeat t (restrict f)))] with x hx he
  rw [he] at hx
  exact sub_nonneg.mp hx

/-- With comparison of the single resolvent steps, the positive constant is
exactly the squared half-time norm of the plateau Dirichlet heat flow. -/
theorem paper_mass_from_smoothing
    (hcmp : ∀ (a : ℝ) (ha : 400 ≤ a) (f : Base), (∀ᵐ x ∂baseMeasure, 0 ≤ f x) →
      ∀ᵐ x ∂baseMeasure, extend (smallSmoothing a ha (restrict f)) x ≤ smoothing a (by linarith) f x)
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (hbpos : ∀ᵐ x ∂baseMeasure, 0 ≤ b x)
    (hbone : ∀ x ∈ plateau, b x = 1) (g : Base)
    (hg : ∀ᵐ x ∂baseMeasure, 0 ≤ g x) (hne : g ≠ 0)
    (hsupp : ∀ᵐ x ∂baseMeasure, x ∉ plateau → g x = 0)
    (h : ℕ → ℝ≥0) (N : ℕ) (T : ℝ≥0) (hT : ∑ k ∈ Finset.range N, h (N - k) = T) :
    0 < ‖smallHeat (T / 2) (restrict g)‖ ^ 2 ∧
    ‖smallHeat (T / 2) (restrict g)‖ ^ 2 ≤
      inner ℝ g (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g 0) := by
  refine ⟨subinterval_heat_energy_positive smallHeat (T / 2) (smallHeat_injective _) g hne hsupp, ?_⟩
  exact initial_pairing_bound smallHeat smallHeat_nonnegative smallHeat_add
    (heat_domination_of_smoothing hcmp) b hb hbound hbpos hbone h N g hg hsupp
    smallHeat_zero smallHeat_symmetric T hT

end HeatSmallIntervalEulerOrder

#print axioms HeatSmallIntervalEulerOrder.heat_domination_of_smoothing
#print axioms HeatSmallIntervalEulerOrder.paper_mass_from_smoothing
