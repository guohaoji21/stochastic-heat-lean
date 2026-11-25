import HeatAnalyticObservabilityTelescoping
import HeatCellMass
import HeatPartitionIntegral
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace HeatAnalyticTimeObservation

open Filter MeasureTheory Set SHE.PredictableL2
open scoped NNReal

private theorem young {θ k x y ε : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hk : 0 ≤ k) (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 < ε) :
    k * x ^ (1 - θ) * y ^ θ ≤ ε * x + k ^ (1 / θ) * ε ^ (-((1 - θ) / θ)) * y := by
  let c := k ^ (1 / θ) * ε ^ (-((1 - θ) / θ))
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg hk _) (Real.rpow_nonneg hε.le _)
  have hscale : c ^ θ = k / ε ^ (1 - θ) := by
    dsimp only [c]
    rw [Real.mul_rpow (Real.rpow_nonneg hk _) (Real.rpow_nonneg hε.le _),
      ← Real.rpow_mul hk, ← Real.rpow_mul hε.le,
      show (1 / θ) * θ = 1 by field_simp,
      show -((1 - θ) / θ) * θ = -(1 - θ) by field_simp,
      Real.rpow_one, Real.rpow_neg hε.le, div_eq_mul_inv]
  have hmean := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hθ₁.le) hθ.le
    (mul_nonneg hε.le hx) (mul_nonneg hc hy) (show 1 - θ + θ = 1 by ring)
  rw [Real.mul_rpow hε.le hx, Real.mul_rpow hc hy, hscale] at hmean
  have he : ε ^ (1 - θ) * x ^ (1 - θ) * (k / ε ^ (1 - θ) * y ^ θ) =
      k * x ^ (1 - θ) * y ^ θ := by
    field_simp [(Real.rpow_pos_of_pos hε _).ne']
  rw [he] at hmean
  exact hmean.trans (add_le_add (by nlinarith [mul_nonneg hε.le hx])
    (by nlinarith [mul_nonneg hc hy]))

/-- Average on the first half of a deterministic interval, where the
remaining time in the two-time estimate is at least half the interval length. -/
theorem interval_step {H a b : ℝ≥0} (hab : a < b) (hb : b ≤ H)
    {θ K A B ε : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) (E O : ℝ≥0 → ℝ)
    (hE : ∀ s, 0 ≤ E s) (hO : ∀ s, 0 ≤ O s) (hi : Integrable O (timeMeasure H))
    (henergy : ∀ {s t : ℝ≥0}, s ≤ t → t ≤ H → E s ≤ K * E t)
    (hinterp : ∀ {s t : ℝ≥0}, s < t → t ≤ H →
      E s ≤ A * Real.exp (B / ((t : ℝ) - s)) * E t ^ (1 - θ) * O s ^ θ) :
    E a ≤ ε * E b + 2 * (K * A) ^ (1 / θ) * ε ^ (-((1 - θ) / θ)) *
      Real.exp ((2 * B / θ + 1) / ((b : ℝ) - a)) *
        ∫ s in Ioc a b, O s ∂timeMeasure H := by
  let δ : ℝ := (b : ℝ) - a
  let m : ℝ≥0 := (a + b) / 2
  let ν := (timeMeasure H).restrict (Ioc a m)
  let c := (K * A) ^ (1 / θ) * ε ^ (-((1 - θ) / θ))
  let D := c * Real.exp ((2 * B / θ) / δ)
  have hδ : 0 < δ := sub_pos.mpr (by exact_mod_cast hab)
  have hm : (m : ℝ) = ((a : ℝ) + b) / 2 := rfl
  have ham : a ≤ m := by exact_mod_cast (show (a : ℝ) ≤ m by rw [hm]; dsimp [δ] at hδ; linarith)
  have hmb : m < b := by exact_mod_cast (show (m : ℝ) < b by rw [hm]; dsimp [δ] at hδ; linarith)
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (mul_nonneg hK hA) _) (Real.rpow_nonneg hε.le _)
  have hD : 0 ≤ D := mul_nonneg hc (Real.exp_nonneg _)
  have hpoint (s : ℝ≥0) (hs : s ∈ Ioc a m) : E a ≤ ε * E b + D * O s := by
    have hsm : (s : ℝ) ≤ m := by exact_mod_cast hs.2
    have hgap : δ / 2 ≤ (b : ℝ) - s := by rw [hm] at hsm; dsimp [δ]; linarith
    have hcost : Real.exp (B / ((b : ℝ) - s)) ≤ Real.exp (2 * B / δ) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ B / (δ / 2) := div_le_div_of_nonneg_left hB (by positivity) hgap
        _ = _ := by field_simp
    have he : E a ≤ (K * A * Real.exp (2 * B / δ)) * E b ^ (1 - θ) * O s ^ θ := calc
      E a ≤ K * E s := henergy hs.1.le (hs.2.trans (hmb.le.trans hb))
      _ ≤ K * (A * Real.exp (B / ((b : ℝ) - s)) * E b ^ (1 - θ) * O s ^ θ) :=
        mul_le_mul_of_nonneg_left (hinterp (hs.2.trans_lt hmb) hb) hK
      _ ≤ K * (A * Real.exp (2 * B / δ) * E b ^ (1 - θ) * O s ^ θ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
            (Real.rpow_nonneg (hE b) _)) (Real.rpow_nonneg (hO s) _)) hK
      _ = _ := by ring
    have hy := young hθ hθ₁ (mul_nonneg (mul_nonneg hK hA) (Real.exp_nonneg (2 * B / δ)))
      (hE b) (hO s) hε
    rw [Real.mul_rpow (mul_nonneg hK hA) (Real.exp_nonneg _), ← Real.exp_mul] at hy
    have hfactor : (K * A) ^ (1 / θ) * Real.exp (2 * B / δ * (1 / θ)) * ε ^ (-((1 - θ) / θ)) = D := by
      rw [show 2 * B / δ * (1 / θ) = (2 * B / θ) / δ by ring]
      dsimp [D, c]
      ring
    rw [hfactor] at hy
    exact he.trans hy
  have hmass : ν.real univ = δ / 2 := by
    rw [show ν.real univ = (m : ℝ) - a from HeatCellMass.mass ham (hmb.le.trans hb), hm]
    dsimp [δ]
    ring
  have hoν : Integrable O ν := hi.integrableOn
  have hu := integral_mono_ae (integrable_const (E a) : Integrable (fun _ : ℝ≥0 => E a) ν)
    ((integrable_const (ε * E b)).add (hoν.const_mul D))
    (show ∀ᵐ s ∂ν, E a ≤ ε * E b + D * O s from
      (ae_restrict_mem measurableSet_Ioc).mono fun _ hs => hpoint _ hs)
  change (∫ _ : ℝ≥0, E a ∂ν) ≤ ∫ s, (ε * E b + D * O s) ∂ν at hu
  rw [integral_add (integrable_const _) (hoν.const_mul D), integral_const_mul D O] at hu
  simp only [integral_const, smul_eq_mul, hmass] at hu
  have hhalf : E a ≤ ε * E b + 2 / δ * D * (∫ s, O s ∂ν) := by
    apply (mul_le_mul_iff_left₀ (show 0 < δ / 2 by positivity)).mp
    convert hu using 1 <;> field_simp [hδ.ne']
  have hnon : 0 ≤ ∫ s, O s ∂ν := integral_nonneg hO
  have hsub : (∫ s, O s ∂ν) ≤ ∫ s in Ioc a b, O s ∂timeMeasure H :=
    setIntegral_mono_set hi.integrableOn (ae_of_all _ hO)
      (Eventually.of_forall fun _ hs => ⟨hs.1, hs.2.trans hmb.le⟩)
  have habsorb : (2 / δ) * D ≤ 2 * (K * A) ^ (1 / θ) * ε ^ (-((1 - θ) / θ)) *
      Real.exp ((2 * B / θ + 1) / δ) := calc
    _ = 2 * (1 / δ) * (c * Real.exp ((2 * B / θ) / δ)) := by dsimp only [D]; ring
    _ ≤ 2 * Real.exp (1 / δ) * (c * Real.exp ((2 * B / θ) / δ)) := by
      gcongr
      exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (1 / δ))
    _ = _ := by
      rw [show (2 * B / θ + 1) / δ = 1 / δ + (2 * B / θ) / δ by ring, Real.exp_add]
      dsimp only [c]
      ring
  exact hhalf.trans (add_le_add le_rfl (mul_le_mul habsorb hsub hnon (by positivity)))

/-- A uniform two-time estimate gives a uniform endpoint observability bound
on the actual nonnegative time measure. -/
theorem integrated {H : ℝ≥0} (hH : 0 < H) {θ K A B : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (E O : ℝ≥0 → ℝ), (∀ s, 0 ≤ E s) → (∀ s, 0 ≤ O s) →
      Integrable O (timeMeasure H) →
      (∀ {s t : ℝ≥0}, s ≤ t → t ≤ H → E s ≤ K * E t) →
      (∀ {s t : ℝ≥0}, s < t → t ≤ H →
        E s ≤ A * Real.exp (B / ((t : ℝ) - s)) * E t ^ (1 - θ) * O s ^ θ) →
      E 0 ≤ L * ∫ s, O s ∂timeMeasure H := by
  let α := (1 - θ) / θ
  let r := (α + 1) / (α + 2)
  let d := (H : ℝ) * (1 - r)
  let C := 2 * (K * A) ^ (1 / θ)
  let C₀ := 2 * B / θ + 1
  let D := (C₀ + 1) * (α + 1)
  have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hθ₁.le) hθ.le
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₁ : r < 1 := (div_lt_one (show 0 < α + 2 by positivity)).mpr (by linarith)
  have hd : 0 < d := mul_pos (by exact_mod_cast hH) (sub_pos.mpr hr₁)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.rpow_nonneg (mul_nonneg hK hA) _)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hweight : C₀ ≤ D * (1 - α * (r⁻¹ - 1)) := by
    have he : D * (1 - α * (r⁻¹ - 1)) = C₀ + 1 := by
      dsimp only [D, r]
      rw [inv_div]
      field_simp [show α + 1 ≠ 0 by positivity]
      ring
    rw [he]
    linarith
  refine ⟨C * Real.exp (D / d), mul_nonneg hC (Real.exp_nonneg _), ?_⟩
  intro E O hE hO hi hg hstep
  let t (n : ℕ) := ((H : ℝ) * (1 - r ^ n)).toNNReal
  let Q (n : ℕ) := ∫ s in Ioc (t n) (t (n+1)), O s ∂timeMeasure H
  have ht (n : ℕ) : (t n : ℝ) = (H : ℝ) * (1 - r ^ n) :=
    Real.coe_toNNReal _ (mul_nonneg H.property (sub_nonneg.mpr (pow_le_one₀ hr.le hr₁.le)))
  have ht0 : t 0 = 0 := by apply NNReal.coe_injective; simp [ht]
  have htH (n : ℕ) : t n ≤ H := by
    exact_mod_cast (show (t n : ℝ) ≤ H by
      rw [ht]
      calc
        _ ≤ (H : ℝ) * 1 := mul_le_mul_of_nonneg_left (sub_le_self 1 (pow_nonneg hr.le n)) H.property
        _ = _ := mul_one _)
  have hdist (n : ℕ) : (t (n+1) : ℝ) - t n = d * r ^ n := by rw [ht, ht, pow_succ]; dsimp [d]; ring
  have htlt (n : ℕ) : t n < t (n+1) := by
    exact_mod_cast (sub_pos.mp (show 0 < (t (n+1) : ℝ) - t n by rw [hdist]; positivity))
  have hmono : Monotone t := monotone_nat_of_le_succ fun n => (htlt n).le
  have hQ (n : ℕ) : ∑ k ∈ Finset.range n, Q k ≤ ∫ s, O s ∂timeMeasure H := by
    change (∑ k ∈ Finset.range n, ∫ s in Ioc (t k) (t (k+1)), O s ∂timeMeasure H) ≤ _
    rw [HeatPartitionIntegral.cells O hi t hmono]
    exact setIntegral_le_integral hi (ae_of_all _ hO)
  have htelescope := HeatAnalyticObservabilityTelescoping.telescope r d α C C₀ D
    (∫ s, O s ∂timeMeasure H) (K * E H) hr hr₁ hd hC hD hweight
    (fun n => E (t n)) Q (fun n => hE (t n)) (fun n => hg (htH n) le_rfl)
    (fun _ => integral_nonneg hO) hQ
    (fun n ε hε => by
      have hs := interval_step (htlt n) (htH (n+1)) hθ hθ₁ hK hA hB hε E O hE hO hi hg hstep
      rw [hdist] at hs
      exact hs)
  simpa only [ht0] using htelescope

end HeatAnalyticTimeObservation

#print axioms HeatAnalyticTimeObservation.interval_step
#print axioms HeatAnalyticTimeObservation.integrated
