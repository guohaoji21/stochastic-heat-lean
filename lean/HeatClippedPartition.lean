import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace HeatClippedPartition
open Filter Finset
open scoped NNReal BigOperators

def raw (d : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := ∑ k∈range n,d k

def nodes (d : ℕ → ℝ≥0) (H : ℝ≥0) (n : ℕ) : ℝ≥0 := min H (raw d n)

theorem raw_succ (d : ℕ → ℝ≥0) (n : ℕ) : raw d (n+1)=raw d n+d n :=
  Finset.sum_range_succ _ _

theorem raw_mono (d : ℕ → ℝ≥0) : Monotone (raw d) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [raw_succ]
  exact le_add_of_nonneg_right (by positivity)

theorem nodes_mono (d : ℕ → ℝ≥0) (H : ℝ≥0) : Monotone (nodes d H) :=
  fun _ _ h => min_le_min_left _ (raw_mono d h)

theorem exists_end (d : ℕ → ℝ≥0) (H : ℝ≥0) (hH : 0<H)
    (hd : Tendsto (fun n => (raw d n:ℝ)) atTop atTop) :
    ∃ N : ℕ,1 ≤ N ∧ raw d (N-1)<H ∧ H ≤ raw d N := by
  have hex : ∃ n,H ≤ raw d n := by
    obtain ⟨n,hn⟩ := (hd.eventually_ge_atTop (H:ℝ)).exists
    exact ⟨n,by exact_mod_cast hn⟩
  let N := Nat.find hex
  have hend : H ≤ raw d N := Nat.find_spec hex
  have hN : 1 ≤ N := by
    by_contra hn
    have hz : N=0 := by omega
    rw [hz] at hend
    have hh : H ≤ 0 := by simpa [raw] using hend
    exact (not_le_of_gt hH) hh
  refine ⟨N,hN,?_,hend⟩
  exact lt_of_not_ge (Nat.find_min hex (by omega : N-1<N))

theorem node_before (d : ℕ → ℝ≥0) (H : ℝ≥0) {N : ℕ}
    (hbefore : raw d (N-1)<H) (n : ℕ) (hn : n<N) :
    nodes d H n=raw d n := by
  exact min_eq_right (le_of_lt ((raw_mono d (by omega : n ≤ N-1)).trans_lt hbefore))

theorem node_after (d : ℕ → ℝ≥0) (H : ℝ≥0) {N : ℕ}
    (hend : H ≤ raw d N) (n : ℕ) (hn : N ≤ n) : nodes d H n=H := by
  exact min_eq_left (hend.trans (raw_mono d hn))

theorem nodes_properties (d : ℕ → ℝ≥0) (H : ℝ≥0) (hdpos : ∀ n,0<d n)
    {N : ℕ} (hN : 1 ≤ N) (hbefore : raw d (N-1)<H) (hend : H ≤ raw d N) :
    nodes d H 0=0 ∧ nodes d H N=H ∧
      (∀ n,n<N → nodes d H n<nodes d H (n+1)) ∧
      (∀ n,nodes d H n ≤ H) := by
  refine ⟨by simp [nodes,raw],node_after d H hend N le_rfl,?_,fun n => min_le_left _ _⟩
  intro n hn
  rw [node_before d H hbefore n hn]
  apply lt_min
  · exact (raw_mono d (by omega : n ≤ N-1)).trans_lt hbefore
  · rw [raw_succ]
    exact lt_add_of_pos_right _ (hdpos n)

theorem full_length (d : ℕ → ℝ≥0) (H : ℝ≥0) {N : ℕ}
    (hbefore : raw d (N-1)<H) {j : ℕ} (hj : 1 ≤ j) (hjN : j<N) :
    nodes d H j-nodes d H (j-1)=d (j-1) := by
  rw [node_before d H hbefore j hjN,node_before d H hbefore (j-1) (by omega)]
  have he : j=(j-1)+1 := by omega
  conv_lhs => rw [he]
  simp only [Nat.add_sub_cancel,raw_succ,add_tsub_cancel_left]

theorem last_length_bound (d : ℕ → ℝ≥0) (H : ℝ≥0) {N : ℕ}
    (hN : 1 ≤ N) (hbefore : raw d (N-1)<H) (hend : H ≤ raw d N) :
    nodes d H N-nodes d H (N-1) ≤ d (N-1) := by
  rw [node_after d H hend N le_rfl,node_before d H hbefore (N-1) (by omega)]
  apply tsub_le_iff_right.mpr
  have he : N=(N-1)+1 := by omega
  calc
    H ≤ raw d N := hend
    _ = d (N-1)+raw d (N-1) := by rw [he,raw_succ];simp [add_comm]

theorem length_bound (d : ℕ → ℝ≥0) (H : ℝ≥0) {N : ℕ}
    (hN : 1 ≤ N) (hbefore : raw d (N-1)<H) (hend : H ≤ raw d N)
    {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    nodes d H j-nodes d H (j-1) ≤ d (j-1) := by
  rcases lt_or_eq_of_le hjN with hl | he
  · exact (full_length d H hbefore hj hl).le
  · subst j
    exact last_length_bound d H hN hbefore hend

theorem lengths_antitone (d : ℕ → ℝ≥0) (H : ℝ≥0) (hd : Antitone d) {N : ℕ}
    (hN : 1 ≤ N) (hbefore : raw d (N-1)<H) (hend : H ≤ raw d N)
    {j : ℕ} (hj : 1 ≤ j) :
    nodes d H (j+1)-nodes d H j ≤ nodes d H j-nodes d H (j-1) := by
  by_cases hjN : j<N
  · rw [full_length d H hbefore hj hjN]
    calc
      _ ≤ d j := by simpa only [Nat.add_sub_cancel] using
        length_bound d H hN hbefore hend (j := j+1) (by omega) (by omega)
      _ ≤ d (j-1) := hd (Nat.sub_le j 1)
  · have hNj : N ≤ j := by omega
    rw [node_after d H hend (j+1) (by omega),node_after d H hend j hNj,tsub_self]
    exact bot_le

theorem reverse_sum (t : ℕ → ℝ≥0) (ht : Monotone t) : ∀ N,
    (∑ k∈range N,(t (N-k)-t (N-k-1)))=t N-t 0 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    have he : (∑ k∈range N,(t (N+1-(k+1))-t (N+1-(k+1)-1)))=
        ∑ k∈range N,(t (N-k)-t (N-k-1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Nat.add_sub_add_right]
    rw [he,ih]
    simp only [Nat.sub_zero,Nat.add_sub_cancel]
    rw [add_comm]
    exact tsub_add_tsub_cancel (ht (Nat.le_succ N)) (ht (Nat.zero_le N))

end HeatClippedPartition
#check @HeatClippedPartition.exists_end
#print axioms HeatClippedPartition.exists_end
#check @HeatClippedPartition.nodes_properties
#print axioms HeatClippedPartition.nodes_properties
#check @HeatClippedPartition.full_length
#print axioms HeatClippedPartition.full_length
#check @HeatClippedPartition.last_length_bound
#print axioms HeatClippedPartition.last_length_bound

#check @HeatClippedPartition.length_bound
#print axioms HeatClippedPartition.length_bound

#check @HeatClippedPartition.lengths_antitone
#print axioms HeatClippedPartition.lengths_antitone

#check @HeatClippedPartition.reverse_sum
#print axioms HeatClippedPartition.reverse_sum
