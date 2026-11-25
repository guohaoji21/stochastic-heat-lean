import HeatDualityEndpoints
import SHE.ProcessEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatTimePartition
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem selected_cell (n : ℕ) (f : ℕ → ℝ≥0 × Ω → E) :
    (fun p : ℝ≥0 × Ω => ∑ k∈Finset.Icc 1 (ApproximationCells.index n H),
      (Ioc (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k)).indicator
        (fun s => f k (s,p.2)) p.1)=ᵐ[energyMeasure μ H]
      (fun p => f (ApproximationCells.index n p.1) p) := by
  classical
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
  have hi := ApproximationCells.index_mem n hp.1 hp.2
  have hin : ApproximationCells.index n p.1≠0 := by have := (Finset.mem_Icc.mp hi).1;omega
  rw [Finset.sum_eq_single (ApproximationCells.index n p.1)]
  · rw [Set.indicator_of_mem ((HeatDualityGrid.cell H n _ hin p.1 hp.2).mpr rfl)]
  · intro k hk hki
    have hk0 : k≠0 := by have := (Finset.mem_Icc.mp hk).1;omega
    exact Set.indicator_of_notMem (fun hh => hki ((HeatDualityGrid.cell H n k hk0 p.1 hp.2).mp hh).symm) _
  · intro hnot
    exact False.elim (hnot hi)

theorem integral_selected (n : ℕ) (f : ℕ → ℝ≥0 × Ω → E)
    (hf : ∀ k∈Finset.Icc 1 (ApproximationCells.index n H), Integrable (f k) (energyMeasure μ H)) :
    (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),
      ∫ p, (Ioc (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k)).indicator
        (fun s => f k (s,p.2)) p.1 ∂energyMeasure μ H)=
      ∫ p,f (ApproximationCells.index n p.1) p ∂energyMeasure μ H := by
  rw [←integral_finset_sum]
  · exact integral_congr_ae (selected_cell μ H n f)
  · intro k hk
    exact (hf k hk).indicator (measurableSet_Ioc.preimage measurable_fst)

theorem telescopes (q : ℕ → ℝ) : ∀ N,
    (∑ k∈Finset.Icc 1 N, (q k-q (k-1)))=q N-q 0 := by
  intro N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1),ih,Nat.add_sub_cancel]
    ring

end HeatTimePartition
#check @HeatTimePartition.selected_cell
#print axioms HeatTimePartition.selected_cell
#check @HeatTimePartition.integral_selected
#print HeatTimePartition.integral_selected
#print axioms HeatTimePartition.integral_selected
#check @HeatTimePartition.telescopes
#print axioms HeatTimePartition.telescopes
