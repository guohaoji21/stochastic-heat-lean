import HeatGevreyPeriodization
import HeatPolynomialBarrier
import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatTorusPeriodicBarrier

open Set Filter HeatGevreyPeriodization
open scoped Topology

private abbrev seed (R : ℝ) := HeatPolynomialBarrier.bump (-R) R
private abbrev gradient (R : ℝ) := HeatPolynomialBarrier.gradient (-R) R
private abbrev laplacian (R : ℝ) := HeatPolynomialBarrier.laplacian (-R) R

private theorem seed_zero {R : ℝ} (hR : 0 ≤ R) {x : ℝ} (hx : R ≤ |x|) :
    seed R x = 0 ∧ gradient R x = 0 ∧ laplacian R x = 0 := by
  have hq : HeatPolynomialBarrier.q (-R) R x ≤ 0 := by
    unfold HeatPolynomialBarrier.q
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h] at hx
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    · rw [abs_of_nonpos h] at hx
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  obtain ⟨h₀, h₁, h₂⟩ := HeatPolynomialBarrier.formulas_nonpositive hq
  simp [seed, gradient, laplacian, HeatPolynomialBarrier.bump, HeatPolynomialBarrier.gradient,
    HeatPolynomialBarrier.laplacian, h₀, h₁, h₂]

/-- A nonnegative polynomial barrier on the circle, with an explicit bound
on its lift's second derivative and support in a prescribed arc. -/
theorem exists_barrier {R : ℝ} (hR : 0 < R) (hsmall : R < 1 / 2) (c : UnitAddCircle) :
    ∃ f f' f'' : UnitAddCircle → ℝ, Continuous f ∧ Continuous f' ∧ Continuous f'' ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : UnitAddCircle)) (f' (x : UnitAddCircle)) x) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => f' (y : UnitAddCircle)) (f'' (x : UnitAddCircle)) x) ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1 ∧ 0 ≤ f'' x + (196 / (R - -R)^2) * f x) ∧
      0 < f c ∧ ∀ x, f x ≠ 0 → ∃ y : ℝ, |y| < R ∧ x = c + (y : UnitAddCircle) := by
  have hP : (0 : ℝ) < 1 := by norm_num
  let F := periodize hP (seed R)
  let D := periodize hP (gradient R)
  let E := periodize hP (laplacian R)
  have he (x : ℝ) : ∀ᶠ y in 𝓝 x,
      F y = seed R (y - (toIcoDiv hP (-1/2) x : ℝ)) ∧
      D y = gradient R (y - (toIcoDiv hP (-1/2) x : ℝ)) ∧
      E y = laplacian R (y - (toIcoDiv hP (-1/2) x : ℝ)) := by
    let k := toIcoDiv hP (-1/2) x
    have hk : toIcoMod hP (-1/2) x + (k : ℝ) = x := by
      simpa only [zsmul_eq_mul, mul_one] using toIcoMod_add_toIcoDiv_zsmul hP (-1/2) x
    have hi := toIcoMod_mem_Ico hP (-1/2) x
    have hx : |x - (k : ℝ)| < 1 - R := by
      rw [show x - (k : ℝ) = toIcoMod hP (-1/2) x by linarith]
      apply abs_lt.mpr
      constructor <;> linarith [hi.1, hi.2]
    have ha : Continuous (fun y : ℝ => |y - (k : ℝ)|) := by fun_prop
    filter_upwards [ha.continuousAt.eventually_lt continuousAt_const hx] with y hy
    have hy' : |y - (k : ℝ) * 1| < 1 - R := by simpa only [mul_one] using hy
    refine ⟨?_, ?_, ?_⟩
    · simpa only [mul_one] using
        periodize_eq_shift hP hsmall (fun t ht => (seed_zero hR.le ht).1) k hy'
    · simpa only [mul_one] using
        periodize_eq_shift hP hsmall (fun t ht => (seed_zero hR.le ht).2.1) k hy'
    · simpa only [mul_one] using
        periodize_eq_shift hP hsmall (fun t ht => (seed_zero hR.le ht).2.2) k hy'
  have hD (x : ℝ) : HasDerivAt F (D x) x := by
    let k := toIcoDiv hP (-1/2) x
    have h := (HeatPolynomialBarrier.bump_deriv (-R) R (x - (k : ℝ))).comp x
      ((hasDerivAt_id x).sub_const (k : ℝ))
    have hx := (he x).self_of_nhds
    rw [hx.2.1]
    apply HasDerivAt.congr_of_eventuallyEq (f := fun y : ℝ => seed R (y - (k : ℝ))) _
      ((he x).mono fun _ hy => hy.1)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have hE (x : ℝ) : HasDerivAt D (E x) x := by
    let k := toIcoDiv hP (-1/2) x
    have h := (HeatPolynomialBarrier.gradient_deriv (-R) R (x - (k : ℝ))).comp x
      ((hasDerivAt_id x).sub_const (k : ℝ))
    have hx := (he x).self_of_nhds
    rw [hx.2.2]
    apply HasDerivAt.congr_of_eventuallyEq (f := fun y : ℝ => gradient R (y - (k : ℝ))) _
      ((he x).mono fun _ hy => hy.2.1)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have hcE : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hloc : Continuous (fun y : ℝ => laplacian R (y - (toIcoDiv hP (-1/2) x : ℝ))) := by
      unfold laplacian HeatPolynomialBarrier.laplacian HeatPolynomialBarrier.ddp
        HeatPolynomialBarrier.dp HeatPolynomialBarrier.dq HeatPolynomialBarrier.q
      fun_prop
    exact hloc.continuousAt.congr ((he x).mono fun _ hy => hy.2.2.symm)
  let hFper := periodize_periodic hP (seed R)
  let hDper := periodize_periodic hP (gradient R)
  let hEper := periodize_periodic hP (laplacian R)
  let Q : UnitAddCircle → ℝ := hFper.lift
  let L : UnitAddCircle → ℝ := hDper.lift
  let B : UnitAddCircle → ℝ := hEper.lift
  have hQ : Continuous Q := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
    (continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt)
  have hL : Continuous L := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
    (continuous_iff_continuousAt.mpr fun x => (hE x).continuousAt)
  have hB : Continuous B := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hcE
  obtain ⟨z, hz⟩ := (QuotientAddGroup.mk_surjective : Function.Surjective
    (fun x : ℝ => (x : UnitAddCircle))) c
  let shift : UnitAddCircle → UnitAddCircle := fun x => x - c
  have hcshift : Continuous shift := continuous_id.sub continuous_const
  refine ⟨Q ∘ shift, L ∘ shift, B ∘ shift, hQ.comp hcshift, hL.comp hcshift, hB.comp hcshift,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hd := (hD (x - z)).comp x ((hasDerivAt_id x).sub_const z)
    simpa only [shift, Function.comp_def, id_eq, ← hz, ← AddCircle.coe_sub,
      Q, L, hFper.lift_coe, hDper.lift_coe, mul_one] using hd
  · intro x
    have hd := (hE (x - z)).comp x ((hasDerivAt_id x).sub_const z)
    simpa only [shift, Function.comp_def, id_eq, ← hz, ← AddCircle.coe_sub,
      L, B, hDper.lift_coe, hEper.lift_coe, mul_one] using hd
  · intro x
    obtain ⟨y, hy⟩ := (QuotientAddGroup.mk_surjective : Function.Surjective
      (fun u : ℝ => (u : UnitAddCircle))) (x - c)
    let w := toIcoMod hP (-1/2) y
    change 0 ≤ Q (x - c) ∧ Q (x - c) ≤ 1 ∧ 0 ≤ B (x - c) + _ * Q (x - c)
    rw [← hy]
    change 0 ≤ seed R w ∧ seed R w ≤ 1 ∧ 0 ≤ laplacian R w + _ * seed R w
    refine ⟨HeatPolynomialBarrier.nonnegative _ _ _, ?_, HeatPolynomialBarrier.subeigen (by linarith) w⟩
    change HeatPolynomialBarrier.p (HeatPolynomialBarrier.q (-R) R w) ≤ 1
    rcases le_total 0 (HeatPolynomialBarrier.q (-R) R w) with h | h
    · rw [(HeatPolynomialBarrier.formulas_nonnegative h).1]
      apply pow_le_one₀ h
      unfold HeatPolynomialBarrier.q
      nlinarith [sq_nonneg w, mul_le_mul_of_nonneg_left hsmall.le hR.le]
    · rw [(HeatPolynomialBarrier.formulas_nonpositive h).1]
      norm_num
  · change 0 < Q (c - c)
    rw [sub_self]
    change 0 < Q ((0 : ℝ) : UnitAddCircle)
    change 0 < F 0
    have h := periodize_eq_shift hP hsmall (fun t ht => (seed_zero hR.le ht).1) 0
      (x := 0) (by simp; linarith)
    have hp : 0 < HeatPolynomialBarrier.q (-R) R 0 := by
      simpa [HeatPolynomialBarrier.q] using mul_pos hR hR
    have hq := (HeatPolynomialBarrier.formulas_nonnegative hp.le).1
    simpa only [F, h, Int.cast_zero, zero_mul, sub_zero, seed, HeatPolynomialBarrier.bump, hq]
      using pow_pos hp 4
  · intro x hx
    obtain ⟨y, hy⟩ := (QuotientAddGroup.mk_surjective : Function.Surjective
      (fun u : ℝ => (u : UnitAddCircle))) (x - c)
    let w := toIcoMod hP (-1/2) y
    have hw : (w : UnitAddCircle) = (y : UnitAddCircle) := by
      have h := congrArg (fun t : ℝ => (t : UnitAddCircle))
        (toIcoMod_add_toIcoDiv_zsmul hP (-1/2) y)
      simpa only [w, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
        using h
    change Q (x - c) ≠ 0 at hx
    rw [← hy] at hx
    change seed R w ≠ 0 at hx
    refine ⟨w, lt_of_not_ge (fun h => hx (seed_zero hR.le h).1), ?_⟩
    rw [hw, hy, add_comm, sub_add_cancel]

end HeatTorusPeriodicBarrier

#print axioms HeatTorusPeriodicBarrier.exists_barrier
