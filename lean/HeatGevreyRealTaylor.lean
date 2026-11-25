import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false

namespace HeatGevreyRealTaylor

open Filter Set
open scoped Topology

private theorem geometric_remainder_tendsto (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (R : ℕ → ℝ) (hR : ∀ n, |R n| ≤ C * q ^ (n + 1)) : Tendsto R atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => q ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_succ, zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const q
  have hb : Tendsto (fun n : ℕ => C * q ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hp.const_mul C
  have ha : Tendsto (fun n => |R n|) atTop (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
      (Eventually.of_forall fun n => abs_nonneg (R n)) (Eventually.of_forall hR)
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 ha

/-- Exact geometric bound from the Lagrange remainder on the unit segment. -/
theorem taylor_01_geometric_bound (f : ℝ → ℝ) (C q : ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hderiv : ∀ (n : ℕ) (t : ℝ), |iteratedDeriv n f t| ≤ C * q ^ n * (n.factorial : ℝ))
    (n : ℕ) : |f 1 - taylorWithinEval f n (uIcc (0 : ℝ) 1) 0 1| ≤ C * q ^ (n + 1) := by
  obtain ⟨t, _, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := f)
    (x := (1 : ℝ)) (x₀ := (0 : ℝ)) (n := n) (by norm_num) (hf.of_le (by simp)).contDiffOn
  have heq' : f 1 - taylorWithinEval f n (uIcc (0 : ℝ) 1) 0 1 =
      iteratedDeriv (n + 1) f t / ((n + 1).factorial : ℝ) := by
    simpa only [sub_zero, one_pow, mul_one] using heq
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  rw [heq', abs_div, abs_of_pos hfac]
  exact (div_le_iff₀ hfac).2 (hderiv (n + 1) t)

theorem taylor_01_tendsto (f : ℝ → ℝ) (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hderiv : ∀ (n : ℕ) (t : ℝ), |iteratedDeriv n f t| ≤ C * q ^ n * (n.factorial : ℝ)) :
    Tendsto (fun n => taylorWithinEval f n (uIcc (0 : ℝ) 1) 0 1) atTop (𝓝 (f 1)) := by
  have hsmall := geometric_remainder_tendsto C q hq0 hq1
    (fun n => f 1 - taylorWithinEval f n (uIcc (0 : ℝ) 1) 0 1)
    (taylor_01_geometric_bound f C q hf hderiv)
  simpa only [sub_sub_cancel, sub_zero] using hsmall.const_sub (f 1)

/-- The coefficient series, with unrestricted real derivatives, recovers
the value at the other endpoint of the unit segment. -/
theorem hasSum_01 (f : ℝ → ℝ) (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hderiv : ∀ (n : ℕ) (t : ℝ), |iteratedDeriv n f t| ≤ C * q ^ n * (n.factorial : ℝ)) :
    HasSum (fun n : ℕ => iteratedDeriv n f 0 / (n.factorial : ℝ)) (f 1) := by
  let a : ℕ → ℝ := fun n => iteratedDeriv n f 0 / (n.factorial : ℝ)
  have hbound (k : ℕ) : ‖a k‖ ≤ C * q^k := by
    have hp : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    dsimp only [a]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).2 (hderiv k 0)
  have hs : Summable a := Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hq0 hq1).mul_left C) hbound
  have he (n : ℕ) : taylorWithinEval f n (uIcc (0 : ℝ) 1) 0 1 = ∑ k ∈ Finset.range (n+1), a k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1))
      (hf.contDiffAt.of_le (by simp)) left_mem_uIcc]
    simp only [sub_zero, one_pow, mul_one, smul_eq_mul, a, div_eq_mul_inv, mul_comm]
  have hleft := taylor_01_tendsto f C q hq0 hq1 hf hderiv
  simp_rw [he] at hleft
  have hright := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hu : ∑' n, a n = f 1 := tendsto_nhds_unique hright hleft
  simpa only [hu] using hs.hasSum

/-- The Gevrey-1 bounds force a one-dimensional function flat at a point
to vanish on the whole real line. -/
theorem eq_zero_of_flat (f : ℝ → ℝ) (C ρ : ℝ) (hρ : 0 < ρ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hderiv : ∀ (n : ℕ) (t : ℝ), |iteratedDeriv n f t| ≤ C * ρ ^ n * (n.factorial : ℝ))
    (a : ℝ) (ha : ∀ n : ℕ, iteratedDeriv n f a = 0) : f = 0 := by
  let A : Set ℝ := {x | ∀ᶠ y in 𝓝 x, f y = 0}
  have hflat (a : ℝ) (ha : ∀ n : ℕ, iteratedDeriv n f a = 0) : a ∈ A := by
    filter_upwards [Metric.ball_mem_nhds a (inv_pos.mpr hρ)] with x hx
    by_cases he : a = x
    · subst x
      simpa only [iteratedDeriv_zero] using ha 0
    have hq : ρ * |x - a| < 1 := by
      have hh : |x - a| < ρ⁻¹ := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
      simpa only [mul_inv_cancel₀ hρ.ne'] using mul_lt_mul_of_pos_left hh hρ
    have hr (n : ℕ) : |f x| ≤ C * (ρ * |x - a|) ^ (n + 1) := by
      have hz : taylorWithinEval f n (uIcc a x) a x = 0 := by
        rw [taylor_within_apply]
        apply Finset.sum_eq_zero
        intro k _
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc he)
          (hf.contDiffAt.of_le (by simp)) left_mem_uIcc, ha k, smul_zero]
      obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := f)
        (n := n) he (hf.of_le (by simp)).contDiffOn
      rw [hz, sub_zero] at hy
      have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
      rw [hy, abs_div, abs_mul, abs_of_pos hfac, abs_pow, mul_pow]
      apply (div_le_iff₀ hfac).2
      convert mul_le_mul_of_nonneg_right (hderiv (n + 1) y) (pow_nonneg (abs_nonneg (x - a)) (n + 1)) using 1
      ring
    have hz := geometric_remainder_tendsto C (ρ * |x - a|) (by positivity) hq (fun _ => f x) hr
    exact tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x))) hz
  have hA : A = ⋂ n : ℕ, {x | iteratedDeriv n f x = 0} := by
    ext x
    rw [mem_iInter]
    constructor
    · intro hx n
      have he : f =ᶠ[𝓝 x] (0 : ℝ → ℝ) := hx
      have h := (he.iteratedDeriv n).eq_of_nhds
      simpa using h
    · exact hflat x
  have hclosed : IsClosed A := by
    rw [hA]
    exact isClosed_iInter fun n => isClosed_eq (hf.continuous_iteratedDeriv n (by simp)) continuous_const
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have he : ∀ᶠ y in 𝓝 x, f y = 0 := hx
    obtain ⟨s, hs, hsx⟩ := mem_nhds_iff.mp he
    exact mem_of_superset (hsx.1.mem_nhds hsx.2) fun y hy =>
      mem_of_superset (hsx.1.mem_nhds hy) hs
  have hall := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ ⟨a, hflat a ha⟩
  funext x
  have hx : x ∈ A := hall ▸ mem_univ x
  exact (show ∀ᶠ y in 𝓝 x, f y = 0 from hx).self_of_nhds

end HeatGevreyRealTaylor

#print axioms HeatGevreyRealTaylor.taylor_01_geometric_bound
#print axioms HeatGevreyRealTaylor.hasSum_01
#print axioms HeatGevreyRealTaylor.eq_zero_of_flat
