import SHE.ApproximationCells

set_option autoImplicit false
noncomputable section
namespace HeatDualityGrid
open SHE MeasureTheory Filter Set
open scoped NNReal Topology

def width (n : ℕ) : ℝ≥0 := ⟨ApproximationClock.delta n,(ApproximationClock.delta_pos n).le⟩
def point (H : ℝ≥0) (n k : ℕ) : ℝ≥0 := min (ApproximationCells.point n k) H

theorem monotone (H : ℝ≥0) (n : ℕ) : Monotone (point H n) := by
  intro j k hjk
  apply min_le_min_right
  change ApproximationClock.delta n*(j:ℝ)≤ApproximationClock.delta n*(k:ℝ)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (ApproximationClock.delta_pos n).le

theorem first (H : ℝ≥0) (n : ℕ) : point H n 0=0 := by
  have h0 : ApproximationCells.point n 0=0 := by
    unfold ApproximationCells.point
    apply Subtype.ext
    simp only [Nat.cast_zero,mul_zero]
    rfl
  change min (ApproximationCells.point n 0) H=0
  rw [h0,min_eq_left (show (0:ℝ≥0)≤H from zero_le)]

theorem last (H : ℝ≥0) (n : ℕ) : point H n (ApproximationCells.index n H)=H := by
  apply min_eq_right
  exact (ApproximationClock.right_bounds n H.property).1

theorem cell (H : ℝ≥0) (n k : ℕ) (hk : k≠0) (s : ℝ≥0) (hs : s≤H) :
    s∈Ioc (point H n (k-1)) (point H n k) ↔ ApproximationCells.index n s=k := by
  rw [← ApproximationCells.cell_iff n k hk s]
  unfold point
  simp only [mem_Ioc]
  constructor
  · intro hh
    have hleft : ApproximationCells.point n (k-1)<s := by
      rcases min_lt_iff.mp hh.1 with hl|hr
      · exact hl
      · exact False.elim ((not_lt_of_ge hs) hr)
    exact ⟨hleft,(le_min_iff.mp hh.2).1⟩
  · intro hh
    exact ⟨lt_of_le_of_lt (min_le_left _ _) hh.1,le_min hh.2 hs⟩

theorem size (H : ℝ≥0) (n k : ℕ) : point H n (k+1)-point H n k≤width n := by
  apply (tsub_le_iff_right).mpr
  apply le_trans (min_le_min_right H (show ApproximationCells.point n (k+1)≤ApproximationCells.point n k+width n by
    apply NNReal.coe_le_coe.mp
    change ApproximationClock.delta n*((k+1:ℕ):ℝ)≤ApproximationClock.delta n*(k:ℝ)+ApproximationClock.delta n
    push_cast
    nlinarith))
  rw [add_comm (width n)]
  change min (ApproximationCells.point n k+width n) H≤min (ApproximationCells.point n k) H+width n
  by_cases hh : ApproximationCells.point n k≤H
  · rw [min_eq_left hh]
    exact min_le_left _ _
  · rw [min_eq_right (le_of_not_ge hh)]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (width n).property)

theorem width_tendsto : Tendsto width atTop (𝓝 0) :=
  NNReal.tendsto_coe.mp ApproximationClock.delta_tendsto

end HeatDualityGrid
#check @HeatDualityGrid.monotone
#print axioms HeatDualityGrid.monotone
#check @HeatDualityGrid.first
#print axioms HeatDualityGrid.first
#check @HeatDualityGrid.last
#print axioms HeatDualityGrid.last
#check @HeatDualityGrid.cell
#print axioms HeatDualityGrid.cell
#check @HeatDualityGrid.size
#print axioms HeatDualityGrid.size
#check @HeatDualityGrid.width_tendsto
#print axioms HeatDualityGrid.width_tendsto
