import HeatTorusDirichletComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace HeatTorusDirichletDomination

open Filter MeasureTheory Set UnitAddTorus EllipticPdes.Sobolev
open HeatTorusFourier HeatTorusReal HeatTorusPatchSobolev HeatTorusDirichletComparison
open HeatFlatTorusSmoothLift (covering)
open HeatTorusFundamentalCell (cell)
open scoped NNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
variable (a : Fin d → ℝ) (hU : U ⊆ cell a)
  (hm : MeasurableSet (covering 1 '' U))

private theorem small_step_mono (ho : IsOpen U) (s : ℝ≥0) (f g : L2D U)
    (h : ∀ᵐ x ∂volume.restrict U, f x ≤ g x) :
    ∀ᵐ x ∂volume.restrict U,
      HeatSmallDomainDirichletHeat.resolvent s f x ≤ HeatSmallDomainDirichletHeat.resolvent s g x := by
  let R := HeatSmallDomainDirichletHeat.resolvent (Ω := U) s
  have hfg : ∀ᵐ x ∂volume.restrict U, 0 ≤ (g - f) x := by
    filter_upwards [h, Lp.coeFn_sub g f] with x hx he
    rw [he]
    exact sub_nonneg.mpr hx
  have hp := HeatSmallDomainDirichletHeat.resolvent_nonnegative ho s (g - f) hfg
  change (∀ᵐ x ∂volume.restrict U, 0 ≤ (R (g - f)) x) at hp
  rw [map_sub] at hp
  filter_upwards [hp, Lp.coeFn_sub (R g) (R f)] with x hx he
  rw [he] at hx
  exact sub_nonneg.mp hx

private theorem torus_iterate_nonnegative (s : ℝ≥0) (f : RealState (Fin d))
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x) (n : ℕ) :
    ∀ᵐ x ∂volume, 0 ≤ (((HeatTorusResolvent.step 1 s : RealState (Fin d) → RealState (Fin d))^[n]) f) x := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact HeatTorusResolvent.step_nonnegative 1 s _ ih

private theorem iterate_le_pull (ho : IsOpen U) (hb : Bornology.IsBounded U) (s : ℝ≥0)
    (f : RealState (Fin d)) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) (n : ℕ) :
    ∀ᵐ x ∂volume.restrict U,
      (HeatSmallDomainDirichletHeat.resolvent s ^ n) (pull a hU hm f) x ≤
        pull a hU hm (((HeatTorusResolvent.step 1 s : RealState (Fin d) → RealState (Fin d))^[n]) f) x := by
  induction n with
  | zero =>
    exact Eventually.of_forall fun _ => le_rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, Function.iterate_succ_apply']
    have h₁ := small_step_mono ho s _ _ ih
    have h₂ := resolvent_le_pull a hU hm ho hb s _ (torus_iterate_nonnegative s f hf n)
    filter_upwards [h₁, h₂] with x hx hy using hx.trans hy

/-- The heat flow on the patch, extended by zero, is bounded by the
ambient torus heat flow at unit period. -/
theorem heat_domination (ho : IsOpen U) (hb : Bornology.IsBounded U) (t : ℝ≥0)
    (f : RealState (Fin d)) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, push a hU hm ho.measurableSet
        (HeatSmallDomainDirichletHeat.heat ho hb t (pull a hU hm f)) x ≤
      realHeat 1 t f x := by
  apply push_le a hU hm ho.measurableSet _ _ (HeatTorusGaussian.realHeat_nonnegative 1 t f hf)
  let A (n : ℕ) := HeatSmallDomainDirichletHeat.euler t n (pull a hU hm f)
  let B (n : ℕ) := pull a hU hm
    (((HeatTorusResolvent.step 1 (t / (n : ℝ≥0)) : RealState (Fin d) → RealState (Fin d))^[n]) f)
  let u := HeatSmallDomainDirichletHeat.heat ho hb t (pull a hU hm f)
  let v := pull a hU hm (realHeat 1 t f)
  have hA : Tendsto A atTop (𝓝 u) := HeatSmallDomainDirichletHeat.euler_tendsto_heat ho hb t _
  have hB : Tendsto B atTop (𝓝 v) :=
    ((pull a hU hm).continuous.continuousAt.tendsto.comp (HeatTorusEuler.tendsto_heat 1 t f))
  have hle (n : ℕ) : ∀ᵐ x ∂volume.restrict U, 0 ≤ (B n - A n) x := by
    filter_upwards [iterate_le_pull a hU hm ho hb (t / (n : ℝ≥0)) f hf n,
      Lp.coeFn_sub (B n) (A n)] with x hx he
    rw [he]
    exact sub_nonneg.mpr hx
  obtain ⟨σ, _, hσ⟩ := (tendstoInMeasure_of_tendsto_Lp (hB.sub hA)).exists_seq_tendsto_ae
  filter_upwards [hσ, ae_all_iff.mpr hle, Lp.coeFn_sub v u] with x hx hn he
  have hp := ge_of_tendsto hx (Eventually.of_forall fun n => hn (σ n))
  change 0 ≤ (v - u) x at hp
  rw [he] at hp
  exact sub_nonneg.mp hp

/-- Period rescaling transports the heat flow with the physical squared
length factor. -/
theorem realHeat_unit_coordinates (P : ℝ) (t : ℝ≥0) (f : RealState (Fin d)) :
    realHeat P t f = realHeat 1 (t / Real.toNNReal (P ^ 2) : ℝ≥0) f := by
  apply (Function.LeftInverse.injective (realPart_embed (ι := Fin d)))
  apply (mFourierBasis (d := Fin d)).repr.injective
  apply lp.ext
  funext k
  let r := t / Real.toNNReal (P ^ 2)
  have hf : frequencySquared P k = frequencySquared 1 k / P ^ 2 := by
    unfold frequencySquared
    rw [div_one, div_pow, div_mul_eq_mul_div]
  have hr : (r : ℝ) = (t : ℝ) / P ^ 2 := by
    simp only [r, NNReal.coe_div, Real.coe_toNNReal _ (sq_nonneg P)]
  have hh : -(t : ℝ) * frequencySquared P k = -(r : ℝ) * frequencySquared 1 k := by
    rw [hf, hr]
    simp only [div_eq_mul_inv]
    ring
  change mFourierBasis.repr (embed (realHeat P t f)) k =
    mFourierBasis.repr (embed (realHeat 1 r f)) k
  simp only [mFourierBasis_repr, embed_realHeat, fourierCoeff_heat, multiplier]
  rw [show max (t : ℝ) 0 = (t : ℝ) from max_eq_left t.property,
    show max (r : ℝ) 0 = (r : ℝ) from max_eq_left r.property, hh]

theorem heat_domination_physical (ho : IsOpen U) (hb : Bornology.IsBounded U)
    (P : ℝ) (t : ℝ≥0) (f : RealState (Fin d)) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, push a hU hm ho.measurableSet
        (HeatSmallDomainDirichletHeat.heat ho hb (t / Real.toNNReal (P ^ 2)) (pull a hU hm f)) x ≤
      realHeat P t f x := by
  rw [realHeat_unit_coordinates]
  exact heat_domination a hU hm ho hb _ f hf

end HeatTorusDirichletDomination

#print axioms HeatTorusDirichletDomination.heat_domination
#print axioms HeatTorusDirichletDomination.realHeat_unit_coordinates
#print axioms HeatTorusDirichletDomination.heat_domination_physical
