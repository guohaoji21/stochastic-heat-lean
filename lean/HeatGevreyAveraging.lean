import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
import HeatGevreyWidths

set_option autoImplicit false
noncomputable section

namespace HeatGevreyAveraging

open MeasureTheory intervalIntegral

/-- Convolution with the normalized indicator of the interval of radius `a`. -/
def boxAverage (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in (x - a)..(x + a), f y) / (2 * a)

theorem hasDerivAt_boxAverage {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (boxAverage a f) ((f (x + a) - f (x - a)) / (2 * a)) x := by
  have hprim (z : ℝ) : HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, f y) (f z) z :=
    integral_hasDerivAt_right (hf.intervalIntegrable 0 z)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hplus := (hprim (x + a)).comp x ((hasDerivAt_id x).add_const a)
  have hminus := (hprim (x - a)).comp x ((hasDerivAt_id x).sub_const a)
  have hcalc := (hplus.sub hminus).div_const (2 * a)
  have hfun : (fun u => ((∫ y in (0 : ℝ)..(u + a), f y) -
      ∫ y in (0 : ℝ)..(u - a), f y) / (2 * a)) = boxAverage a f := by
    funext u
    rw [boxAverage, integral_interval_sub_left (hf.intervalIntegrable 0 (u + a))
      (hf.intervalIntegrable 0 (u - a))]
  rw [← hfun]
  simpa only [Function.comp_def, id_eq, Pi.sub_apply, mul_one] using hcalc

theorem norm_boxAverage_le {f : ℝ → ℝ} {a M : ℝ} (ha : 0 < a) (hM : ∀ x, ‖f x‖ ≤ M)
    (x : ℝ) : ‖boxAverage a f x‖ ≤ M := by
  have hlen : x + a - (x - a) = 2 * a := by ring
  have hpos : 0 < 2 * a := by positivity
  rw [boxAverage, norm_div, Real.norm_eq_abs (2 * a), abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  calc
    _ ≤ M * |x + a - (x - a)| := norm_integral_le_of_norm_le_const (fun y _ => hM y)
    _ = M * (2 * a) := by rw [hlen, abs_of_pos hpos]

theorem boxAverage_eq_const {f : ℝ → ℝ} {a x c : ℝ} (ha : 0 < a)
    (hf : ∀ y, |y - x| ≤ a → f y = c) : boxAverage a f x = c := by
  have hab : x - a ≤ x + a := by linarith
  have he : (∫ y in (x-a)..(x+a), f y) = ∫ _ in (x-a)..(x+a), c := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    exact hf y (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  rw [boxAverage, he, intervalIntegral.integral_const,
    show x + a - (x - a) = 2 * a by ring, smul_eq_mul]
  exact mul_div_cancel_left₀ c (mul_pos (by norm_num) ha).ne'

/-- One layer gains one derivative with the reciprocal-radius loss. -/
theorem norm_deriv_boxAverage_le {f : ℝ → ℝ} (hf : Continuous f) {a M : ℝ}
    (ha : 0 < a) (hM : ∀ x, ‖f x‖ ≤ M) (x : ℝ) :
    ‖deriv (boxAverage a f) x‖ ≤ M / a := by
  have hpos : 0 < 2 * a := by positivity
  rw [(hasDerivAt_boxAverage hf a x).deriv, norm_div, Real.norm_eq_abs (2 * a), abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  calc
    ‖f (x + a) - f (x - a)‖ ≤ ‖f (x + a)‖ + ‖f (x - a)‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hM _) (hM _)
    _ = (M / a) * (2 * a) := by
      field_simp
      ring

private theorem contDiff_shift {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (a : ℝ) :
    ContDiff ℝ n (fun x => f (x + a)) :=
  hf.comp (contDiff_id.add contDiff_const)

theorem contDiff_boxAverage {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (a : ℝ) :
    ContDiff ℝ (n + 1 : ℕ) (boxAverage a f) := by
  rw [Nat.cast_succ, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_boxAverage hf.continuous a x).differentiableAt,
    by simp, ?_⟩
  have hd : deriv (boxAverage a f) = fun x => (f (x + a) - f (x - a)) / (2 * a) :=
    funext fun x => (hasDerivAt_boxAverage hf.continuous a x).deriv
  rw [hd]
  exact ((contDiff_shift hf a).sub (by simpa only [sub_eq_add_neg] using contDiff_shift hf (-a))).div_const _

theorem iteratedDeriv_boxAverage {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (a x : ℝ) :
    iteratedDeriv (n + 1) (boxAverage a f) x =
      (iteratedDeriv n f (x + a) - iteratedDeriv n f (x - a)) / (2 * a) := by
  have hd : deriv (boxAverage a f) = fun x => (f (x + a) - f (x - a)) / (2 * a) :=
    funext fun x => (hasDerivAt_boxAverage hf.continuous a x).deriv
  have hm : ContDiff ℝ n (fun x => f (x - a)) := by
    simpa only [sub_eq_add_neg] using contDiff_shift hf (-a)
  rw [iteratedDeriv_succ', hd, iteratedDeriv_div_const,
    iteratedDeriv_fun_sub (contDiff_shift hf a).contDiffAt hm.contDiffAt,
    iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const]

/-- The first width is the radius of the outermost average. -/
def finiteAverage : ℕ → (ℕ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, f => f
  | n+1, a, f => boxAverage (a 0) (finiteAverage n (fun k => a (k+1)) f)

/-- Changes at distance greater than the sum of all radii cannot affect
the value after the finite averaging. -/
theorem finiteAverage_eq_const {f : ℝ → ℝ} (n : ℕ) (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    (x c : ℝ) (hf : ∀ y, |y - x| ≤ ∑ k ∈ Finset.range n, a k → f y = c) :
    finiteAverage n a f x = c := by
  induction n generalizing a x with
  | zero => exact hf x (by simp)
  | succ n ih =>
    rw [finiteAverage]
    apply boxAverage_eq_const (ha 0)
    intro y hy
    apply ih (fun k => a (k+1)) (fun k => ha (k+1)) y
    intro z hz
    apply hf
    rw [Finset.sum_range_succ']
    calc
      |z - x| = |(z - y) + (y - x)| := by ring_nf
      _ ≤ |z - y| + |y - x| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem finiteAverage_top_derivative {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (n : ℕ) (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) :
    ContDiff ℝ n (finiteAverage n a f) ∧
      ∀ x, ‖iteratedDeriv n (finiteAverage n a f) x‖ ≤
        M / ∏ k ∈ Finset.range n, a k := by
  induction n generalizing a with
  | zero => simpa [finiteAverage, contDiff_zero] using And.intro hf hM
  | succ n ih =>
    obtain ⟨hreg, hnorm⟩ := ih (fun k => a (k+1)) (fun k => ha (k+1))
    have hpos : 0 < 2 * a 0 := mul_pos (by norm_num) (ha 0)
    refine ⟨contDiff_boxAverage hreg _, fun x => ?_⟩
    rw [finiteAverage, iteratedDeriv_boxAverage hreg, Finset.prod_range_succ', norm_div,
      Real.norm_eq_abs (2 * a 0), abs_of_pos hpos]
    have hp : 0 < ∏ k ∈ Finset.range n, a (k + 1) := Finset.prod_pos (fun k _ => ha (k + 1))
    apply (div_le_iff₀ hpos).2
    calc
      _ ≤ _ + _ := norm_sub_le _ _
      _ ≤ (M / ∏ k ∈ Finset.range n, a (k + 1)) + M / ∏ k ∈ Finset.range n, a (k + 1) :=
        add_le_add (hnorm _) (hnorm _)
      _ = _ := by
        field_simp [hp.ne', (ha 0).ne']
        ring

theorem finiteAverage_gevrey_bound {f : ℝ → ℝ} (hf : Continuous f) {M a : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (ha : 0 < a) (s : ℝ) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (finiteAverage n (HeatGevreyWidths.width a s) f) x‖ ≤
      M * (((n.factorial : ℝ) ^ s) / a ^ n) := by
  have h := (finiteAverage_top_derivative hf hM n (HeatGevreyWidths.width a s)
    (HeatGevreyWidths.width_pos ha s)).2 x
  simpa only [div_eq_mul_inv, HeatGevreyWidths.width_product_inv a s n] using h

end HeatGevreyAveraging

#print axioms HeatGevreyAveraging.hasDerivAt_boxAverage
#print axioms HeatGevreyAveraging.norm_deriv_boxAverage_le
#print axioms HeatGevreyAveraging.finiteAverage_top_derivative
#print axioms HeatGevreyAveraging.finiteAverage_gevrey_bound
#print axioms HeatGevreyAveraging.finiteAverage_eq_const
