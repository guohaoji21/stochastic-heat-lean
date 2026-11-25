import HeatGevreyAveraging
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
noncomputable section

namespace HeatGevreyLimit

open Filter MeasureTheory intervalIntegral HeatGevreyAveraging
open scoped Topology NNReal

private theorem boxAverage_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a x : ℝ) : boxAverage a (fun y => f y - g y) x = boxAverage a f x - boxAverage a g x := by
  simp only [boxAverage, integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), sub_div]

theorem norm_boxAverage_sub_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a M : ℝ} (ha : 0 < a) (hfg : ∀ x, ‖f x - g x‖ ≤ M) (x : ℝ) :
    ‖boxAverage a f x - boxAverage a g x‖ ≤ M := by
  rw [← boxAverage_sub hf hg]
  exact norm_boxAverage_le ha hfg x

theorem norm_boxAverage_sub_self_le {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {a : ℝ} (ha : 0 < a) (x : ℝ) : ‖boxAverage a f x - f x‖ ≤ (L : ℝ) * a := by
  have hconst : boxAverage a (fun _ => f x) x = f x := boxAverage_eq_const ha (fun _ _ => rfl)
  rw [← hconst, ← boxAverage_sub hf.continuous continuous_const]
  have hab : x - a ≤ x + a := by linarith
  have hlen : x + a - (x - a) = 2 * a := by ring
  have hpos : 0 < 2 * a := mul_pos (by norm_num) ha
  rw [boxAverage, norm_div, Real.norm_eq_abs (2 * a), abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  rw [← abs_of_pos hpos, ← hlen]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  rw [Set.uIoc_of_le hab] at hy
  have hdist : dist y x ≤ a := by
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [← dist_eq_norm]
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)

theorem finiteAverage_contDiff {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) (a : ℕ → ℝ) :
    ContDiff ℝ n (finiteAverage n a f) := by
  induction n generalizing a with
  | zero => simpa [finiteAverage, contDiff_zero] using hf
  | succ n ih => exact contDiff_boxAverage (ih _) _

theorem finiteAverage_norm_le {f : ℝ → ℝ} {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (n : ℕ) (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (x : ℝ) :
    ‖finiteAverage n a f x‖ ≤ M := by
  induction n generalizing a x with
  | zero => exact hM x
  | succ n ih => exact norm_boxAverage_le (ha 0) (ih (fun k => a (k+1)) (fun k => ha (k+1))) x

theorem finiteAverage_stable {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {M : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ M)
    (n : ℕ) (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (x : ℝ) :
    ‖finiteAverage n a f x - finiteAverage n a g x‖ ≤ M := by
  induction n generalizing a x with
  | zero => exact hfg x
  | succ n ih =>
    exact norm_boxAverage_sub_le (finiteAverage_contDiff hf n _).continuous
      (finiteAverage_contDiff hg n _).continuous (ha 0)
      (ih (fun k => a (k+1)) (fun k => ha (k+1))) x

theorem finiteAverage_add (m n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ) :
    finiteAverage (m+n) a f = finiteAverage m a (finiteAverage n (fun k => a (m+k)) f) := by
  induction m generalizing a with
  | zero => simp [finiteAverage]
  | succ m ih =>
    rw [Nat.succ_add, finiteAverage, finiteAverage, ih]
    have hshift : (fun k => a (m+k+1)) = (fun k => a (m+1+k)) := by
      funext k
      exact congrArg a (by omega)
    rw [hshift]

private theorem finiteAverage_step {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (n : ℕ) (x : ℝ) :
    ‖finiteAverage (n+1) a f x - finiteAverage n a f x‖ ≤ (L : ℝ) * a n := by
  have hc : Continuous (boxAverage (a n) f) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_boxAverage hf.continuous (a n) x).continuousAt
  rw [finiteAverage_add]
  exact finiteAverage_stable hc hf.continuous (norm_boxAverage_sub_self_le hf (ha n)) n a ha x

/-- The infinite normalized box convolution of a Lipschitz seed. -/
def limit (a : ℕ → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x + ∑' n, (finiteAverage (n+1) a f x - finiteAverage n a f x)

theorem tendstoUniformly_limit {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hs : Summable a) :
    TendstoUniformly (fun n => finiteAverage n a f) (limit a f) atTop := by
  have ht := tendstoUniformly_tsum_nat (hs.mul_left (L : ℝ)) (finiteAverage_step hf a ha)
  rw [Metric.tendstoUniformly_iff] at ht ⊢
  intro ε hε
  filter_upwards [ht ε hε] with n hn x
  have hn' := hn x
  have hsum := Finset.sum_range_sub (fun n => finiteAverage n a f x) n
  rw [hsum] at hn'
  simp only [limit, Real.dist_eq] at hn' ⊢
  convert hn' using 2
  simp only [finiteAverage]
  ring

theorem limit_continuous {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hs : Summable a) : Continuous (limit a f) :=
  (tendstoUniformly_limit hf a ha hs).continuous
    (Frequently.of_forall fun n => (finiteAverage_contDiff hf.continuous n a).continuous)

theorem limit_norm_le {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hs : Summable a) (x : ℝ) : ‖limit a f x‖ ≤ M :=
  le_of_tendsto' ((tendstoUniformly_limit hf a ha hs).tendsto_at x).norm
    (fun n => finiteAverage_norm_le hM n a ha x)

theorem limit_eq_const {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hs : Summable a) (x c : ℝ)
    (hconst : ∀ y, |y - x| ≤ ∑' k, a k → f y = c) : limit a f x = c := by
  apply tendsto_nhds_unique_of_forall (tendstoUniformly_limit hf a ha hs |>.tendsto_at x) tendsto_const_nhds
  intro n
  apply finiteAverage_eq_const n a ha x c
  intro y hy
  exact hconst y (hy.trans (hs.sum_le_tsum _ (fun k _ => (ha k).le)))

/-- Passing to the limit commutes with the first `m` averages.  This gives
derivative information at order `m` from the continuity of the tail alone. -/
theorem limit_eq_finiteAverage {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hs : Summable a) (m : ℕ) :
    limit a f = finiteAverage m a (limit (fun k => a (m+k)) f) := by
  let b : ℕ → ℝ := fun k => a (m+k)
  have hb (k : ℕ) : 0 < b k := ha _
  have hbs : Summable b := by
    simpa only [b, add_comm] using (summable_nat_add_iff (f := a) m).mpr hs
  have ht := tendstoUniformly_limit hf b hb hbs
  have hc := limit_continuous hf b hb hbs
  have hu : TendstoUniformly (fun n => finiteAverage (m+n) a f) (finiteAverage m a (limit b f)) atTop := by
    rw [Metric.tendstoUniformly_iff] at ht ⊢
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    filter_upwards [ht (ε/2) hhalf] with n hn x
    have hn' (y : ℝ) : ‖finiteAverage n b f y - limit b f y‖ ≤ ε / 2 := by
      simpa only [dist_comm, dist_eq_norm] using (hn y).le
    have hnx := finiteAverage_stable (finiteAverage_contDiff hf.continuous n b).continuous
      hc hn' m a ha x
    rw [finiteAverage_add]
    rw [dist_comm, dist_eq_norm]
    exact hnx.trans_lt (half_lt_self hε)
  funext x
  have hfirst : Tendsto (fun n => finiteAverage (m+n) a f x) atTop (𝓝 (limit a f x)) := by
    simpa only [Function.comp_def, add_comm] using
      ((tendstoUniformly_limit hf a ha hs).tendsto_at x).comp (tendsto_add_atTop_nat m)
  exact tendsto_nhds_unique hfirst (hu.tendsto_at x)

theorem limit_contDiff_and_bound {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hs : Summable a) (n : ℕ) :
    ContDiff ℝ n (limit a f) ∧
      ∀ x, ‖iteratedDeriv n (limit a f) x‖ ≤ M / ∏ k ∈ Finset.range n, a k := by
  rw [limit_eq_finiteAverage hf a ha hs n]
  have ht : Summable (fun k => a (n+k)) := by
    simpa only [add_comm] using (summable_nat_add_iff (f := a) n).mpr hs
  exact finiteAverage_top_derivative (limit_continuous hf _ (fun k => ha (n+k)) ht)
    (limit_norm_le hf hM _ (fun k => ha (n+k)) ht) n a ha

theorem limit_mem_Icc {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hM : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hs : Summable a) (x : ℝ) :
    limit a f x ∈ Set.Icc (0 : ℝ) 1 := by
  have hnorm (n : ℕ) (c : ℝ) (hc : ∀ x, ‖f x - c‖ ≤ 1) : ‖finiteAverage n a f x - c‖ ≤ 1 := by
    have h := finiteAverage_stable hf.continuous (g := fun _ => c) continuous_const hc n a ha x
    rwa [finiteAverage_eq_const n a ha x c (fun _ _ => rfl)] at h
  have hlim := (tendstoUniformly_limit hf a ha hs).tendsto_at x
  have hu := le_of_tendsto' hlim.norm fun n => by
    simpa only [sub_zero] using hnorm n 0 (fun y => by
      simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (hM y).1] using (hM y).2)
  have hl := le_of_tendsto' (hlim.sub_const 1).norm fun n =>
    hnorm n 1 (fun y => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hM y).1, (hM y).2])
  rw [Real.norm_eq_abs, abs_le] at hu hl
  exact ⟨by linarith [hl.1], hu.2⟩

end HeatGevreyLimit

#print axioms HeatGevreyLimit.tendstoUniformly_limit
#print axioms HeatGevreyLimit.limit_contDiff_and_bound
#print axioms HeatGevreyLimit.limit_eq_const
#print axioms HeatGevreyLimit.limit_mem_Icc
