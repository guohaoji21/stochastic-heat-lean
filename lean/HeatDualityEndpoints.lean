import HeatDualityGrid

set_option autoImplicit false
noncomputable section
namespace HeatDualityEndpoints
open SHE MeasureTheory Filter Set
open scoped NNReal Topology

def left (H : ℝ≥0) (n : ℕ) (s : ℝ≥0) : ℝ≥0 :=
  HeatDualityGrid.point H n (ApproximationCells.index n s-1)
def right (H : ℝ≥0) (n : ℕ) (s : ℝ≥0) : ℝ≥0 :=
  HeatDualityGrid.point H n (ApproximationCells.index n s)

theorem bounds (H : ℝ≥0) (n : ℕ) {s : ℝ≥0} (hs0 : 0<s) (hsH : s≤H) :
    left H n s<s ∧ s≤right H n s ∧ right H n s-left H n s≤HeatDualityGrid.width n := by
  have hi : 1≤ApproximationCells.index n s := (Finset.mem_Icc.mp (ApproximationCells.index_mem n hs0 hsH)).1
  have hcell := (HeatDualityGrid.cell H n (ApproximationCells.index n s) (by omega) s hsH).mpr rfl
  refine ⟨hcell.1,hcell.2,?_⟩
  have hh := HeatDualityGrid.size H n (ApproximationCells.index n s-1)
  change HeatDualityGrid.point H n (ApproximationCells.index n s)-
    HeatDualityGrid.point H n (ApproximationCells.index n s-1)≤HeatDualityGrid.width n
  simpa only [Nat.sub_add_cancel hi] using hh

theorem left_tendsto (H : ℝ≥0) {s : ℝ≥0} (hs0 : 0<s) (hsH : s≤H) :
    Tendsto (fun n => left H n s) atTop (𝓝 s) := by
  have hlo (n : ℕ) : s-HeatDualityGrid.width n≤left H n s := by
    have hb := bounds H n hs0 hsH
    have hr : right H n s≤HeatDualityGrid.width n+left H n s := tsub_le_iff_right.mp hb.2.2
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using hb.2.1.trans hr
  have hlim : Tendsto (fun n => s-HeatDualityGrid.width n) atTop (𝓝 s) := by
    simpa only [tsub_zero] using tendsto_const_nhds.sub HeatDualityGrid.width_tendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo (fun n => (bounds H n hs0 hsH).1.le)

theorem right_tendsto (H : ℝ≥0) {s : ℝ≥0} (hs0 : 0<s) (hsH : s≤H) :
    Tendsto (fun n => right H n s) atTop (𝓝 s) := by
  have hhi (n : ℕ) : right H n s≤HeatDualityGrid.width n+s := by
    have hb := bounds H n hs0 hsH
    have hr : right H n s≤HeatDualityGrid.width n+left H n s := tsub_le_iff_right.mp hb.2.2
    exact hr.trans (add_le_add le_rfl hb.1.le)
  have hlim : Tendsto (fun n => HeatDualityGrid.width n+s) atTop (𝓝 s) := by
    simpa only [zero_add] using HeatDualityGrid.width_tendsto.add_const s
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => (bounds H n hs0 hsH).2.1) hhi

theorem measurable (H : ℝ≥0) (n : ℕ) : Measurable (left H n) ∧ Measurable (right H n) := by
  have hi : Measurable (ApproximationCells.index n) :=
    Nat.measurable_ceil.comp (measurable_coe_nnreal_real.div_const (ApproximationClock.delta n))
  exact ⟨(StronglyMeasurable.of_discrete (f := fun k : ℕ => HeatDualityGrid.point H n (k-1))).measurable.comp hi,
    (StronglyMeasurable.of_discrete (f := HeatDualityGrid.point H n)).measurable.comp hi⟩

end HeatDualityEndpoints
#check @HeatDualityEndpoints.bounds
#print axioms HeatDualityEndpoints.bounds
#check @HeatDualityEndpoints.left_tendsto
#print axioms HeatDualityEndpoints.left_tendsto
#check @HeatDualityEndpoints.right_tendsto
#print axioms HeatDualityEndpoints.right_tendsto
#check @HeatDualityEndpoints.measurable
#print axioms HeatDualityEndpoints.measurable
