import HeatAnalyticLocalL2
import HeatAnalyticRealLipschitz
import HeatGevreyAxisBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace HeatAnalyticOpenPropagation

open MeasureTheory Metric Set UnitAddTorus
open HeatTorusGaussian (wrap)
open HeatGevreyFourierExtension (tube)
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The nonnegative squared norm used in the observation integrals. -/
def energy (g : UnitAddTorus ι → E) (x : UnitAddTorus ι) : ℝ≥0∞ :=
  ENNReal.ofReal (‖g x‖ ^ 2)

private theorem lifted_box_energy (g : UnitAddTorus ι → E) {O : Set (UnitAddTorus ι)}
    (hO : MeasurableSet O) (c : ι → ℝ) {r : ℝ} (hr : 2 * r < 1 / 2)
    (hbox : ball c (2 * r) ⊆ wrap ⁻¹' O) :
    (∫⁻ y in ball c (2 * r), energy g (wrap y)) ≤ ∫⁻ x in O, energy g x := by
  let a : ι → ℝ := fun i => c i - 1 / 2
  let D : Set (ι → ℝ) := {z | ∀ i, z i ∈ Ioc (a i) (a i + 1)}
  have hD : MeasurableSet D := MeasurableSet.univ_pi' (fun i => measurableSet_Ioc (a := a i))
  have hsub : ball c (2 * r) ⊆ D := by
    intro y hy i
    have hd : ‖y - c‖ < 2 * r := by simpa only [dist_eq_norm] using mem_ball.mp hy
    have hi : |y i - c i| < 1 / 2 := ((norm_le_pi_norm (y - c) i).trans_lt (hd.trans hr)).trans_le le_rfl
    obtain ⟨hl, hu⟩ := abs_lt.mp hi
    exact ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  calc
    _ = ∫⁻ y, (ball c (2 * r)).indicator (fun y => energy g (wrap y)) y :=
      (lintegral_indicator measurableSet_ball _).symm
    _ ≤ ∫⁻ y, D.indicator (fun y => O.indicator (energy g) (wrap y)) y := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ ball c (2 * r)
      · rw [indicator_of_mem hy, indicator_of_mem (hsub hy),
          indicator_of_mem (show wrap y ∈ O from hbox hy)]
      · rw [indicator_of_notMem hy]
        exact zero_le
    _ = ∫⁻ y in D, O.indicator (energy g) (wrap y) := lintegral_indicator hD _
    _ = ∫⁻ x : UnitAddTorus ι, O.indicator (energy g) x := (UnitAddTorus.lintegral_preimage _ a).symm
    _ = _ := lintegral_indicator hO _

variable [NormedSpace ℂ E] [CompleteSpace E]

/-- Quantitative propagation from any nonempty open observation set on the
unit torus. The constants depend only on the open set and the tube width. -/
theorem squared_energy_interpolation {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : (ι → ℂ) → E) (g : UnitAddTorus ι → E) (M : ℝ), 0 < M →
        DifferentiableOn ℂ F (tube ρ) → (∀ z ∈ tube ρ, ‖F z‖ ≤ M) →
        (∀ (z : ι → ℂ) (m : ι → ℤ), F (z + fun i => (m i : ℂ)) = F z) →
        (∀ x : ι → ℝ, g (wrap x) = F (fun i => (x i : ℂ))) →
        (∫⁻ x, energy g x) ≤ ENNReal.ofReal
          (C * M ^ 2 * (((∫⁻ x in O, energy g x).toReal / M ^ 2) ^ θ)) := by
  classical
  have hwrap := HeatGevreyAxisBridge.wrap_isQuotientMap (ι := ι)
  obtain ⟨p, hp⟩ := hOne
  obtain ⟨c, hc⟩ := hwrap.surjective p
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hwrap.continuous) c (by simpa only [mem_preimage, hc])
  let r := min (R / 4) (min (ρ / 200) (1 / 8))
  have hr : 0 < r := by positivity
  have hrR : r ≤ R / 4 := min_le_left _ _
  have hrρ : r ≤ ρ / 200 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hrρ' : 100 * r < ρ := by linarith
  have hbox : ball c (2 * r) ⊆ wrap ⁻¹' O := (ball_subset_ball (by linarith)).trans hball
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / r)
  let k := n + 1
  have hk : (1 : ℝ) ≤ (k + 1 : ℝ) * r := by
    have hn' := (div_lt_iff₀ hr).mp hn
    dsimp only [k]
    push_cast
    linarith
  let τ : ℝ := (↑(Fintype.card ι + 2) : ℝ)⁻¹
  let β : ℝ := τ * (1 / 2 : ℝ) ^ k
  let θ : ℝ := 2 * β
  let D := (4 : ℝ) / (2 * r) ^ Fintype.card ι
  have hD : 0 < D := by positivity
  have hθ : 0 < θ := by positivity
  have hτ : τ ≤ 1 / 2 := by
    rw [one_div]
    change (↑(Fintype.card ι + 2) : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹
    apply (inv_le_inv₀ (by positivity : 0 < (↑(Fintype.card ι + 2) : ℝ)) (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast (show 2 ≤ Fintype.card ι + 2 by omega)
  have hθ1 : θ < 1 := by
    have hb : (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
      dsimp only [k]
      rw [pow_succ]
      exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
    have hm := mul_le_mul hτ hb (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    dsimp only [θ, β]
    linarith
  refine ⟨(289 : ℝ) ^ 2 * D ^ θ, θ, by positivity, hθ, hθ1, ?_⟩
  intro F g M hM hF hcap hperiod hreal
  let A := (∫⁻ x in O, energy g x).toReal
  have hg (x : UnitAddTorus ι) : ‖g x‖ ≤ M := by
    obtain ⟨z, rfl⟩ := hwrap.surjective x
    rw [hreal]
    apply hcap
    apply mem_iInter.mpr
    intro i
    simp [hρ, neg_lt_zero.mpr hρ]
  have hfinite : (∫⁻ x in O, energy g x) ≠ ∞ := by
    have hb : (∫⁻ x in O, energy g x) ≤ ENNReal.ofReal (M ^ 2) := by
      calc
        _ ≤ ∫⁻ x : UnitAddTorus ι, ENNReal.ofReal (M ^ 2) := by
          rw [← lintegral_indicator hO.measurableSet]
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ O
          · rw [indicator_of_mem hx]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hg x) 2)
          · rw [indicator_of_notMem hx]
            exact zero_le
        _ = _ := by simp [lintegral_const]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hlocal : (∫⁻ y in ball c (2 * r), ENNReal.ofReal (‖F (fun i => (y i : ℂ))‖ ^ 2)) ≤ ENNReal.ofReal A := by
    have h := lifted_box_energy g hO.measurableSet c (by linarith : 2 * r < 1 / 2) hbox
    dsimp only [A]
    rw [ENNReal.ofReal_toReal hfinite]
    simpa only [energy, hreal] using h
  let q := D * (A / M ^ 2)
  have hq : 0 ≤ q := by positivity
  let ε := M * q ^ τ
  have hε : 0 ≤ ε := by positivity
  have hsmall (x : ι → ℝ) (hx : ∀ i, |x i - c i| ≤ r) : ‖F (fun i => (x i : ℂ))‖ ≤ ε := by
    have hx' : x ∈ closedBall c r := by
      rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hr.le]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hx
    have hLip (y : ι → ℝ) :
        ‖F (fun i => (x i : ℂ)) - F (fun i => (y i : ℂ))‖ ≤ (M / (ρ / 2)) * ‖x - y‖ :=
      HeatAnalyticRealLipschitz.real_slice_norm_sub_le hρ hF hcap y x
    have hscale : 2 * (M / (ρ / 2)) * r ≤ M := by
      calc
        _ = M * ((2 * r) / (ρ / 2)) := by ring
        _ ≤ M := mul_le_of_le_one_right hM.le ((div_le_one₀ (by positivity)).mpr (by linarith))
    have h := HeatAnalyticLocalL2.norm_le_of_local_energy (fun y : ι → ℝ => F (fun i => (y i : ℂ)))
      c x hr hM (by positivity) hscale hA hx' (by simpa only [hreal] using hg (wrap x)) hLip hlocal
    have hqeq : 4 * A / (M ^ 2 * (2 * r) ^ Fintype.card ι) = q := by
      dsimp only [q, D]
      rw [div_mul_div_comm]
      ring
    simpa only [hqeq, ε, τ] using h
  have ht (x : UnitAddTorus ι) : ‖g x‖ ≤ 289 * M * q ^ β := by
    obtain ⟨y, rfl⟩ := hwrap.surjective x
    rw [hreal]
    have hp := HeatAnalyticPeriodicPropagation.box_to_periodic_slice (P := 1) one_pos hr hrρ' hM hε hF hcap
      (fun z m => by simpa only [Complex.ofReal_one, one_mul] using hperiod z m)
      c hsmall k hk y
    have hnorm : ε / M = q ^ τ := by dsimp only [ε]; rw [mul_comm, mul_div_cancel_right₀ _ hM.ne']
    rw [hnorm, ← Real.rpow_mul hq] at hp
    exact hp
  have hcoef : (289 * M * q ^ β) ^ 2 = (289 : ℝ) ^ 2 * D ^ θ * M ^ 2 * (A / M ^ 2) ^ θ := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (q ^ β) 2, ← Real.rpow_mul hq]
    have he : β * (↑(2 : ℕ) : ℝ) = θ := by dsimp only [θ]; push_cast; ring
    rw [he]
    dsimp only [q]
    rw [Real.mul_rpow hD.le (by positivity)]
    ring
  calc
    _ ≤ ∫⁻ _x : UnitAddTorus ι, ENNReal.ofReal ((289 * M * q ^ β) ^ 2) :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (ht x) 2)
    _ = _ := by simp [lintegral_const, hcoef, A]

end HeatAnalyticOpenPropagation

#print axioms HeatAnalyticOpenPropagation.squared_energy_interpolation
