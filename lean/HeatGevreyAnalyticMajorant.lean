import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace HeatGevreyAnalyticMajorant

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The homogeneous component of degree `n` of a multivariate power series. -/
def homogeneous (c : (ι → ℕ) → ℂ) (z : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ α ∈ univ.piAntidiag n, c α * ∏ i, z i ^ α i

theorem norm_homogeneous_le (c : (ι → ℕ) → ℂ) (z : ι → ℂ) (C ρ : ℝ) (n : ℕ)
    (hcoeff : ∀ α ∈ (univ : Finset ι).piAntidiag n,
      ‖c α‖ ≤ C * ρ ^ n * (Nat.multinomial univ α : ℝ)) :
    ‖homogeneous c z n‖ ≤ C * (ρ * ∑ i, ‖z i‖) ^ n := by
  classical
  unfold homogeneous
  calc
    _ ≤ ∑ α ∈ univ.piAntidiag n, ‖c α * ∏ i, z i ^ α i‖ := norm_sum_le _ _
    _ ≤ ∑ α ∈ univ.piAntidiag n,
        C * ρ ^ n * ((Nat.multinomial univ α : ℝ) * ∏ i, ‖z i‖ ^ α i) := by
      apply sum_le_sum
      intro α hα
      rw [norm_mul, norm_prod, ← mul_assoc]
      simp_rw [norm_pow]
      exact mul_le_mul_of_nonneg_right (hcoeff α hα) (prod_nonneg fun i _ => by positivity)
    _ = _ := by
      rw [← mul_sum, ← sum_pow_eq_sum_piAntidiag, mul_pow, mul_assoc]

theorem norm_taylor_coefficient_le (D : (ι → ℕ) → ℂ) (C ρ : ℝ) (n : ℕ)
    {α : ι → ℕ} (hα : α ∈ (univ : Finset ι).piAntidiag n)
    (hD : ‖D α‖ ≤ C * ρ ^ n * (n.factorial : ℝ)) :
    ‖D α / (∏ i, (α i).factorial : ℕ)‖ ≤
      C * ρ ^ n * (Nat.multinomial univ α : ℝ) := by
  have hd : ∑ i, α i = n := (mem_piAntidiag.mp hα).1
  have hm := Nat.multinomial_spec (univ : Finset ι) α
  rw [hd] at hm
  have hcast : ((∏ i, (α i).factorial : ℕ) : ℝ) * (Nat.multinomial univ α : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast hm
  have hpos : 0 < ((∏ i, (α i).factorial : ℕ) : ℝ) := by
    exact_mod_cast prod_pos (fun i _ => Nat.factorial_pos (α i))
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hpos).2
  calc
    ‖D α‖ ≤ C * ρ ^ n * (n.factorial : ℝ) := hD
    _ = C * ρ ^ n * (Nat.multinomial univ α : ℝ) *
        ((∏ i, (α i).factorial : ℕ) : ℝ) := by rw [← hcast]; ring

/-- The geometric majorant bounds both the absolute sum and the analytic
series on the `ℓ¹` ball in the recentered complex coordinates. -/
theorem summable_homogeneous_and_bound (c : (ι → ℕ) → ℂ) (z : ι → ℂ) (C ρ : ℝ)
    (hρ : 0 ≤ ρ) (hr : ρ * ∑ i, ‖z i‖ < 1)
    (hcoeff : ∀ n, ∀ α ∈ (univ : Finset ι).piAntidiag n,
      ‖c α‖ ≤ C * ρ ^ n * (Nat.multinomial univ α : ℝ)) :
    Summable (fun n => ‖homogeneous c z n‖) ∧
      ‖∑' n, homogeneous c z n‖ ≤ C / (1 - ρ * ∑ i, ‖z i‖) := by
  have hr₀ : 0 ≤ ρ * ∑ i, ‖z i‖ := mul_nonneg hρ (sum_nonneg fun _ _ => norm_nonneg _)
  have hgeom := (summable_geometric_of_lt_one hr₀ hr).mul_left C
  have hb (n : ℕ) := norm_homogeneous_le c z C ρ n (hcoeff n)
  refine ⟨hgeom.of_nonneg_of_le (fun n => norm_nonneg _) hb, ?_⟩
  have h := tsum_of_norm_bounded hgeom.hasSum hb
  rwa [tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr, ← div_eq_mul_inv] at h

/-- The recentered Gevrey-1 Taylor series is bounded by `2*C` on any
polydisc whose radius times the dimension and Gevrey constant is at most `1/2`. -/
theorem taylor_polydisc_bound (D : (ι → ℕ) → ℂ) (z : ι → ℂ) (C ρ r : ℝ)
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hr : ρ * ((Fintype.card ι : ℝ) * r) ≤ 1 / 2)
    (hz : ∀ i, ‖z i‖ ≤ r)
    (hD : ∀ n, ∀ α ∈ (univ : Finset ι).piAntidiag n,
      ‖D α‖ ≤ C * ρ ^ n * (n.factorial : ℝ)) :
    let c := fun α : ι → ℕ => D α / (∏ i, (α i).factorial : ℕ)
    Summable (fun n => ‖homogeneous c z n‖) ∧ ‖∑' n, homogeneous c z n‖ ≤ 2 * C := by
  dsimp only
  have hsum : ∑ i, ‖z i‖ ≤ (Fintype.card ι : ℝ) * r := by
    simpa using sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hz i)
  have hhalf : ρ * ∑ i, ‖z i‖ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hsum hρ).trans hr
  obtain ⟨hs, hb⟩ := summable_homogeneous_and_bound
    (fun α => D α / (∏ i, (α i).factorial : ℕ)) z C ρ hρ (by linarith)
    (fun n α hα => norm_taylor_coefficient_le D C ρ n hα (hD n α hα))
  refine ⟨hs, hb.trans ((div_le_iff₀ (by linarith)).2 ?_)⟩
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hhalf)]

end HeatGevreyAnalyticMajorant

#print axioms HeatGevreyAnalyticMajorant.norm_taylor_coefficient_le
#print axioms HeatGevreyAnalyticMajorant.summable_homogeneous_and_bound
#print axioms HeatGevreyAnalyticMajorant.taylor_polydisc_bound
