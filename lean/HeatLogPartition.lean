import HeatLogPartitionClock
import HeatClippedPartition

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatLogPartition
open Filter Finset
open scoped NNReal BigOperators

def lengths (L : ℝ) (hL : 1 ≤ L) (n : ℕ) : ℝ≥0 :=
  ⟨(HeatLogPartitionClock.ell L n)⁻¹,inv_nonneg.mpr (by have := HeatLogPartitionClock.one_le L hL n;linarith)⟩

theorem positive (L : ℝ) (hL : 1 ≤ L) (n : ℕ) : 0<lengths L hL n := by
  change (0:ℝ)<(HeatLogPartitionClock.ell L n)⁻¹
  exact inv_pos.mpr (by have := HeatLogPartitionClock.one_le L hL n;linarith)

theorem antitone (L : ℝ) (hL : 1 ≤ L) : Antitone (lengths L hL) := by
  have hm : Monotone (HeatLogPartitionClock.ell L) := by
    apply monotone_nat_of_le_succ
    intro n
    have he := HeatLogPartitionClock.recurrence L n
    have hp : 0<Real.log (2*HeatLogPartitionClock.ell L n) :=
      Real.log_pos (by have := HeatLogPartitionClock.one_le L hL n;linarith)
    linarith
  intro i j hij
  change (HeatLogPartitionClock.ell L j)⁻¹ ≤ (HeatLogPartitionClock.ell L i)⁻¹
  exact inv_le_inv₀ (by have := HeatLogPartitionClock.one_le L hL j;linarith)
    (by have := HeatLogPartitionClock.one_le L hL i;linarith) |>.mpr (hm hij)

theorem le_one (L : ℝ) (hL : 1 ≤ L) (n : ℕ) : lengths L hL n ≤ 1 := by
  change (HeatLogPartitionClock.ell L n)⁻¹ ≤ (1:ℝ)
  exact inv_le_one_of_one_le₀ (HeatLogPartitionClock.one_le L hL n)

theorem exists_partition (L : ℝ) (hL : 1 ≤ L) (H : ℝ≥0) (hH : 0<H) :
    ∃ N : ℕ,1 ≤ N ∧ HeatClippedPartition.raw (lengths L hL) (N-1)<H ∧
      H ≤ HeatClippedPartition.raw (lengths L hL) N := by
  apply HeatClippedPartition.exists_end (lengths L hL) H hH
  have he : (fun n => (HeatClippedPartition.raw (lengths L hL) n:ℝ))=
      fun n => ∑ k∈range n,(HeatLogPartitionClock.ell L k)⁻¹ := by
    funext n
    change ((∑ k∈range n,lengths L hL k : ℝ≥0):ℝ)=_
    exact NNReal.coe_sum (range n) (lengths L hL)
  rw [he]
  exact HeatLogPartitionClock.reciprocal_sum_tends_top L hL

end HeatLogPartition
#check @HeatLogPartition.positive
#print axioms HeatLogPartition.positive
#check @HeatLogPartition.antitone
#print axioms HeatLogPartition.antitone
#check @HeatLogPartition.le_one
#print axioms HeatLogPartition.le_one
#check @HeatLogPartition.exists_partition
#print axioms HeatLogPartition.exists_partition
