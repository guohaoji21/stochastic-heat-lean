import HeatGevreyCutoff
import Mathlib.Algebra.Order.ToIntervalMod

set_option autoImplicit false
noncomputable section

namespace HeatGevreyPeriodization

open Set Filter
open scoped Topology

/-- The periodic extension of a seed supported inside the centered period interval. -/
def periodize {P : ℝ} (hP : 0 < P) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (toIcoMod hP (-P/2) x)

theorem periodize_periodic {P : ℝ} (hP : 0 < P) (f : ℝ → ℝ) :
    Function.Periodic (periodize hP f) P := by
  intro x
  rw [periodize, toIcoMod_add_right, periodize]

private theorem representative_abs_le {P : ℝ} (hP : 0 < P) (x : ℝ) :
    |toIcoMod hP (-P/2) x| ≤ P/2 := by
  have hx := toIcoMod_mem_Ico hP (-P/2) x
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem abs_int_sub_ge_one {k j : ℤ} (h : k ≠ j) : 1 ≤ |(k : ℝ) - j| := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have hstep : k + 1 ≤ j := by omega
    rw [abs_of_nonpos (by exact_mod_cast (sub_nonpos.mpr hlt.le : k-j ≤ 0))]
    exact_mod_cast (show (1 : ℤ) ≤ -(k-j) by omega)
  · have hstep : j + 1 ≤ k := by omega
    rw [abs_of_nonneg (by exact_mod_cast (sub_nonneg.mpr hlt.le : 0 ≤ k-j))]
    exact_mod_cast (show (1 : ℤ) ≤ k-j by omega)

theorem periodize_eq_shift {P R : ℝ} (hP : 0 < P) (hR : R < P/2)
    {f : ℝ → ℝ} (hzero : ∀ t, R ≤ |t| → f t = 0)
    (k : ℤ) {x : ℝ} (hx : |x - (k : ℝ) * P| < P - R) :
    periodize hP f x = f (x - (k : ℝ) * P) := by
  let j := toIcoDiv hP (-P/2) x
  let y := toIcoMod hP (-P/2) x
  let z := x - (k : ℝ) * P
  have hy : |y| ≤ P/2 := representative_abs_le hP x
  have hyj : y + (j : ℝ) * P = x := by
    simpa only [zsmul_eq_mul] using toIcoMod_add_toIcoDiv_zsmul hP (-P/2) x
  change f y = f z
  by_cases hkj : k = j
  · have he : y = z := by
      dsimp only [z]
      rw [hkj]
      linarith
    rw [he]
  · have heq : z - y = ((j : ℝ) - k) * P := by dsimp [z]; linarith
    have hd : P ≤ |z-y| := by
      rw [heq, abs_mul, abs_of_pos hP]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (abs_int_sub_ge_one (Ne.symm hkj)) hP.le
    have hsum : |z-y| ≤ |z| + |y| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le z 0 y
    have hz : |z| < P-R := hx
    rw [hzero y (by linarith), hzero z (by linarith [hR])]

theorem periodize_eventuallyEq {P R : ℝ} (hP : 0 < P) (hR : R < P/2)
    {f : ℝ → ℝ} (hzero : ∀ t, R ≤ |t| → f t = 0) (x : ℝ) :
    ∃ k : ℤ, periodize hP f =ᶠ[𝓝 x] fun y => f (y - (k : ℝ) * P) := by
  let k := toIcoDiv hP (-P/2) x
  have hx : |x - (k : ℝ) * P| < P-R := by
    have he : x - (k : ℝ) * P = toIcoMod hP (-P/2) x := by
      have h := toIcoMod_add_toIcoDiv_zsmul hP (-P/2) x
      rw [zsmul_eq_mul] at h
      dsimp only [k]
      linarith
    rw [he]
    exact (representative_abs_le hP x).trans_lt (by linarith)
  have hc : Continuous (fun y : ℝ => |y - (k : ℝ) * P|) := by fun_prop
  refine ⟨k, ?_⟩
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const hx] with y hy
  exact periodize_eq_shift hP hR hzero k hy

theorem periodize_contDiff {P R : ℝ} (hP : 0 < P) (hR : R < P/2)
    {f : ℝ → ℝ} (hzero : ∀ t, R ≤ |t| → f t = 0) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (periodize hP f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨k, hk⟩ := periodize_eventuallyEq hP hR hzero x
  exact (hf.comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq hk

theorem periodize_derivative_bound {P R s ρ : ℝ} (hP : 0 < P) (hR : R < P/2)
    {f : ℝ → ℝ} (hzero : ∀ t, R ≤ |t| → f t = 0)
    (hf : ∀ (n : ℕ) x, ‖iteratedDeriv n f x‖ ≤ ρ ^ n * (n.factorial : ℝ) ^ s)
    (n : ℕ) (x : ℝ) : ‖iteratedDeriv n (periodize hP f) x‖ ≤ ρ ^ n * (n.factorial : ℝ) ^ s := by
  obtain ⟨k, hk⟩ := periodize_eventuallyEq hP hR hzero x
  rw [(hk.iteratedDeriv n).eq_of_nhds, iteratedDeriv_comp_sub_const]
  exact hf n _

theorem exists_periodic_cutoff {P s r R : ℝ} (hP : 0 < P) (hs : 1 < s) (hr : 0 < r)
    (hrR : r < R) (hR : R < P/2) :
    ∃ b : ℝ → ℝ, ∃ ρ : ℝ, 0 < ρ ∧ Function.Periodic b P ∧ ContDiff ℝ (⊤ : ℕ∞) b ∧
      (∀ x, b x ∈ Icc 0 1) ∧ (∀ x, |x| ≤ r → b x = 1) ∧
      (∀ x, R ≤ |toIcoMod hP (-P/2) x| → b x = 0) ∧
      ∀ (n : ℕ) x, ‖iteratedDeriv n b x‖ ≤ ρ ^ n * (n.factorial : ℝ) ^ s := by
  obtain ⟨f, ρ, hρ, hf, h01, h1, hS, _, hD⟩ := HeatGevreyCutoff.exists_cutoff hs hr hrR
  have hzero (t : ℝ) (ht : R ≤ |t|) : f t = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have ht' := hS hm
    exact (not_lt_of_ge ht) (abs_lt.mpr ⟨ht'.1, ht'.2⟩)
  refine ⟨periodize hP f, ρ, hρ, periodize_periodic hP f, periodize_contDiff hP hR hzero hf,
    fun x => h01 _, ?_, fun x hx => hzero _ hx, periodize_derivative_bound hP hR hzero hD⟩
  intro x hx
  have hx' : |x - ((0 : ℤ) : ℝ) * P| < P-R := by
    simp
    linarith
  rw [periodize_eq_shift hP hR hzero 0 hx']
  simpa using h1 x hx

end HeatGevreyPeriodization

#print axioms HeatGevreyPeriodization.periodize_eventuallyEq
#print axioms HeatGevreyPeriodization.exists_periodic_cutoff
