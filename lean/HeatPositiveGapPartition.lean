import HeatLogClock
import HeatClippedPartition
import HeatPartitionDecay

set_option autoImplicit false
noncomputable section

namespace HeatPositiveGapPartition

open Filter Finset
open scoped NNReal BigOperators

/-- The inverse cell lengths for an arbitrary positive separation constant. -/
def inverseLengths (κ L : ℝ) : ℕ → ℝ
  | 0 => L
  | n + 1 => inverseLengths κ L n + Real.log (2 * inverseLengths κ L n) / κ

variable {κ L : ℝ} (hκ : 0 < κ) (hL : 1 ≤ L)
include hκ hL

theorem inverseLengths_one_le : ∀ n, 1 ≤ inverseLengths κ L n := by
  intro n
  induction n with
  | zero => exact hL
  | succ n ih =>
    have hlog : 0 ≤ Real.log (2 * inverseLengths κ L n) := Real.log_nonneg (by linarith)
    exact le_trans ih (le_add_of_nonneg_right (div_nonneg hlog hκ.le))

omit hL in
theorem recurrence (n : ℕ) :
    κ * (inverseLengths κ L (n + 1) - inverseLengths κ L n) =
      Real.log (2 * inverseLengths κ L n) := by
  rw [inverseLengths, add_sub_cancel_left, mul_div_cancel₀ _ hκ.ne']

theorem inverseLengths_monotone : Monotone (inverseLengths κ L) := by
  apply monotone_nat_of_le_succ
  intro n
  have hlog : 0 ≤ Real.log (2 * inverseLengths κ L n) :=
    Real.log_nonneg (by linarith [inverseLengths_one_le hκ hL n])
  exact le_add_of_nonneg_right (div_nonneg hlog hκ.le)

def lengths (n : ℕ) : ℝ≥0 :=
  ⟨(inverseLengths κ L n)⁻¹,
    inv_nonneg.mpr (zero_le_one.trans (inverseLengths_one_le hκ hL n))⟩

theorem lengths_positive (n : ℕ) : 0 < lengths hκ hL n :=
  inv_pos.mpr (zero_lt_one.trans_le (inverseLengths_one_le hκ hL n))

theorem lengths_antitone : Antitone (lengths hκ hL) := by
  intro i j hij
  change (inverseLengths κ L j)⁻¹ ≤ (inverseLengths κ L i)⁻¹
  exact (inv_le_inv₀ (zero_lt_one.trans_le (inverseLengths_one_le hκ hL j))
    (zero_lt_one.trans_le (inverseLengths_one_le hκ hL i))).mpr
      (inverseLengths_monotone hκ hL hij)

theorem lengths_le_one (n : ℕ) : lengths hκ hL n ≤ 1 :=
  inv_le_one_of_one_le₀ (inverseLengths_one_le hκ hL n)

private theorem inverseLengths_lower : ∀ n : ℕ,
    L + (n : ℝ) * (Real.log 2 / κ) ≤ inverseLengths κ L n := by
  intro n
  induction n with
  | zero => simp [inverseLengths]
  | succ n ih =>
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ 2 * inverseLengths κ L n by
        linarith [inverseLengths_one_le hκ hL n])
    have hstep := div_le_div_of_nonneg_right hlog hκ.le
    simp only [inverseLengths, Nat.cast_succ]
    linarith

private theorem inverseLengths_tends_top : Tendsto (inverseLengths κ L) atTop atTop := by
  have hc : 0 < Real.log 2 / κ := div_pos (Real.log_pos (by norm_num)) hκ
  exact tendsto_atTop_mono (inverseLengths_lower hκ hL)
    (tendsto_atTop_add_const_left _ L (tendsto_natCast_atTop_atTop.atTop_mul_const hc))

omit hL in
private theorem loglog_step {x y : ℝ} (hx : 1 ≤ x)
    (hrec : κ * (y - x) = Real.log (2 * x)) :
    κ * (Real.log (Real.log (2 * y)) - Real.log (Real.log (2 * x))) ≤ x⁻¹ := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlx : 0 < Real.log (2 * x) := Real.log_pos (by linarith)
  have hd : Real.log (2 * x) / κ = y - x :=
    (div_eq_iff hκ.ne').2 (by simpa only [mul_comm] using hrec.symm)
  have hdiff : 0 < y - x := by
    rw [← hd]
    exact div_pos hlx hκ
  have hy : 0 < y := by linarith
  have hly : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  have houter := HeatLogClock.log_increment (Real.log (2 * x)) (Real.log (2 * y)) hlx hly
  have hinner := HeatLogClock.log_increment (2 * x) (2 * y) (by positivity) (by positivity)
  calc
    _ ≤ κ * (((2 * y - 2 * x) / (2 * x)) / Real.log (2 * x)) :=
      mul_le_mul_of_nonneg_left
        (houter.trans (div_le_div_of_nonneg_right hinner hlx.le)) hκ.le
    _ = x⁻¹ := by
      field_simp
      nlinarith [hrec]

theorem reciprocal_sum_lower : ∀ n,
    κ * (Real.log (Real.log (2 * inverseLengths κ L n)) - Real.log (Real.log (2 * L))) ≤
      ∑ k ∈ range n, (inverseLengths κ L k)⁻¹ := by
  intro n
  induction n with
  | zero => simp [inverseLengths]
  | succ n ih =>
    have hstep := loglog_step hκ (inverseLengths_one_le hκ hL n) (recurrence (L := L) hκ n)
    rw [sum_range_succ]
    linarith

theorem reciprocal_sum_tends_top :
    Tendsto (fun n => ∑ k ∈ range n, (inverseLengths κ L k)⁻¹) atTop atTop := by
  have h2 := (inverseLengths_tends_top hκ hL).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hlog := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h2)
  exact tendsto_atTop_mono (reciprocal_sum_lower hκ hL)
    ((tendsto_atTop_add_const_right _ (-Real.log (Real.log (2 * L))) hlog).const_mul_atTop hκ)

theorem exists_partition (T : ℝ≥0) (hT : 0 < T) :
    ∃ N : ℕ, 1 ≤ N ∧ HeatClippedPartition.raw (lengths hκ hL) (N - 1) < T ∧
      T ≤ HeatClippedPartition.raw (lengths hκ hL) N := by
  apply HeatClippedPartition.exists_end (lengths hκ hL) T hT
  have he : (fun n => (HeatClippedPartition.raw (lengths hκ hL) n : ℝ)) =
      fun n => ∑ k ∈ range n, (inverseLengths κ L k)⁻¹ := by
    funext n
    exact NNReal.coe_sum (range n) (lengths hκ hL)
  rw [he]
  exact reciprocal_sum_tends_top hκ hL

/-- The geometric observation bound survives shortening the last cell. -/
theorem clipped_sum_bound (T : ℝ≥0) {N : ℕ} (hN : 1 ≤ N)
    (hbefore : HeatClippedPartition.raw (lengths hκ hL) (N - 1) < T)
    (hend : T ≤ HeatClippedPartition.raw (lengths hκ hL) N) :
    let t := HeatClippedPartition.nodes (lengths hκ hL) T
    (∑ n ∈ range N, Real.exp (-κ / ((t (n + 1) - t n : ℝ≥0) : ℝ)) *
      (∏ k ∈ range n, (((t (k + 1) - t k : ℝ≥0) : ℝ))⁻¹)) ≤
        2 * Real.exp (-κ * L) := by
  let d := lengths hκ hL
  let t := HeatClippedPartition.nodes d T
  have hprops := HeatClippedPartition.nodes_properties d T (lengths_positive hκ hL)
    hN hbefore hend
  have hpos (n : ℕ) : 0 < inverseLengths κ L n :=
    zero_lt_one.trans_le (inverseLengths_one_le hκ hL n)
  have hcell (n : ℕ) (hn : n < N) :
      Real.exp (-κ / ((t (n + 1) - t n : ℝ≥0) : ℝ)) *
        (∏ k ∈ range n, (((t (k + 1) - t k : ℝ≥0) : ℝ))⁻¹) ≤
      Real.exp (-κ * inverseLengths κ L n) * (∏ k ∈ range n, inverseLengths κ L k) := by
    have hstep : 0 < ((t (n + 1) - t n : ℝ≥0) : ℝ) := by
      exact_mod_cast (tsub_pos_iff_lt.mpr (hprops.2.2.1 n hn))
    have hlength := HeatClippedPartition.length_bound d T hN hbefore hend
      (j := n + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hlength
    have hlength' : ((t (n + 1) - t n : ℝ≥0) : ℝ) ≤ (d n : ℝ) := by
      exact_mod_cast hlength
    have hinv : inverseLengths κ L n ≤ ((t (n + 1) - t n : ℝ≥0) : ℝ)⁻¹ := by
      simpa [d, lengths] using
        (inv_le_inv₀ (inv_pos.mpr (hpos n)) hstep).mpr hlength'
    have hprod : (∏ k ∈ range n, (((t (k + 1) - t k : ℝ≥0) : ℝ))⁻¹) =
        ∏ k ∈ range n, inverseLengths κ L k := by
      apply prod_congr rfl
      intro k hk
      have hk' : k < n := mem_range.mp hk
      have hfull := HeatClippedPartition.full_length d T hbefore
        (j := k + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hfull
      rw [hfull]
      exact inv_inv (inverseLengths κ L k)
    rw [hprod]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonpos_left hinv (neg_nonpos.mpr hκ.le)))
      (prod_nonneg fun k _ => (hpos k).le)
  exact (sum_le_sum fun n hn => hcell n (mem_range.mp hn)).trans
    (HeatPartitionDecay.recurrence_sum_bound κ (inverseLengths κ L) hpos
      (recurrence hκ) N)

end HeatPositiveGapPartition

#print axioms HeatPositiveGapPartition.exists_partition
#print axioms HeatPositiveGapPartition.clipped_sum_bound
