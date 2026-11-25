import HeatLogPartition
import HeatPartitionDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatGridDecay
open Filter Finset
open scoped NNReal BigOperators

theorem sum_bound (L : ℝ) (hL : 1 ≤ L) (H : ℝ≥0) {N : ℕ} (hN : 1 ≤ N)
    (hbefore : HeatClippedPartition.raw (HeatLogPartition.lengths L hL) (N-1)<H)
    (hend : H ≤ HeatClippedPartition.raw (HeatLogPartition.lengths L hL) N) :
    let t := HeatClippedPartition.nodes (HeatLogPartition.lengths L hL) H
    (∑ n∈range N,Real.exp (-4/((t (n+1)-t n:ℝ≥0):ℝ))*
      (∏ k∈range n,(((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) ≤ 2*Real.exp (-4*L) := by
  let d := HeatLogPartition.lengths L hL
  let t := HeatClippedPartition.nodes d H
  have hprops := HeatClippedPartition.nodes_properties d H (HeatLogPartition.positive L hL) hN hbefore hend
  have hpoint (n : ℕ) (hn : n<N) :
      Real.exp (-4/((t (n+1)-t n:ℝ≥0):ℝ))*(∏ k∈range n,(((t (k+1)-t k:ℝ≥0):ℝ))⁻¹) ≤
        Real.exp (-4*HeatLogPartitionClock.ell L n)*(∏ k∈range n,HeatLogPartitionClock.ell L k) := by
    have hpos : 0<((t (n+1)-t n:ℝ≥0):ℝ) := by
      exact_mod_cast (tsub_pos_iff_lt.mpr (hprops.2.2.1 n hn))
    have hb : ((t (n+1)-t n:ℝ≥0):ℝ) ≤ (HeatLogPartitionClock.ell L n)⁻¹ := by
      have hh := HeatClippedPartition.length_bound d H hN hbefore hend (j := n+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hh
      have hhcast : ((t (n+1)-t n:ℝ≥0):ℝ) ≤ (d n:ℝ) := by exact_mod_cast hh
      exact hhcast
    have hx : 0<HeatLogPartitionClock.ell L n := by have := HeatLogPartitionClock.one_le L hL n;linarith
    have hinv : HeatLogPartitionClock.ell L n ≤ 1/((t (n+1)-t n:ℝ≥0):ℝ) := by
      apply (le_div_iff₀ hpos).mpr
      have hm := (le_div_iff₀ hx).mp (show ((t (n+1)-t n:ℝ≥0):ℝ) ≤ 1/HeatLogPartitionClock.ell L n by simpa only [one_div] using hb)
      nlinarith
    have he : Real.exp (-4/((t (n+1)-t n:ℝ≥0):ℝ)) ≤ Real.exp (-4*HeatLogPartitionClock.ell L n) := by
      apply Real.exp_le_exp.mpr
      simp only [div_eq_mul_inv,one_mul] at hinv ⊢
      linarith
    have hp : (∏ k∈range n,(((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)=∏ k∈range n,HeatLogPartitionClock.ell L k := by
      apply Finset.prod_congr rfl
      intro k hk
      have hklt : k<n := Finset.mem_range.mp hk
      have hf := HeatClippedPartition.full_length d H hbefore (j := k+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hf
      rw [hf]
      exact inv_inv (HeatLogPartitionClock.ell L k)
    rw [hp]
    apply mul_le_mul_of_nonneg_right he
    exact Finset.prod_nonneg fun k _ => by have := HeatLogPartitionClock.one_le L hL k;linarith
  have hsum := Finset.sum_le_sum (fun n hn => hpoint n (Finset.mem_range.mp hn))
  have hdec := HeatPartitionDecay.recurrence_sum_bound 4 (HeatLogPartitionClock.ell L)
    (fun n => by have := HeatLogPartitionClock.one_le L hL n;linarith)
    (HeatLogPartitionClock.recurrence L) N
  exact hsum.trans (by simpa only [HeatLogPartitionClock.ell] using hdec)

end HeatGridDecay
#check @HeatGridDecay.sum_bound
#print axioms HeatGridDecay.sum_bound
