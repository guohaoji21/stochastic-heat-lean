import HeatTimePartition
import HeatMixedCellBound
import HeatDualityRemainder

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatPartitionEnergy
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem sum_energy (n : ℕ) (u : Process (E := E) F μ H) :
    (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),
      HeatMixedCellBound.energy F μ H (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k) u)=‖u‖^2 := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hh := HeatTimePartition.integral_selected μ H n (fun _ p => ‖u p‖^2) (fun _ _ => hu.norm.integrable_sq)
  change _=(∫ p,‖u p‖^2 ∂energyMeasure μ H) at hh
  exact hh.trans (subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F) u).symm

variable (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

def mixed (u v : Process (E := E) F μ H) (n k : ℕ) : ℝ :=
  let a := HeatDualityGrid.point H n (k-1)
  let b := HeatDualityGrid.point H n k
  inner ℝ (((S (HeatDualityGrid.width n-(b-a))).compLpL 2 μ)
    (I.integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u)))
    (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v)

theorem mixed_bound (hM : ‖M‖≤1) (u v : Process (E := E) F μ H) (n : ℕ) :
    |∑ k∈Finset.Icc 1 (ApproximationCells.index n H),mixed F μ H S hS hcontr M I u v n k|≤
      Real.sqrt (HeatDualityGrid.width n:ℝ)*Real.sqrt (‖u‖^2)*Real.sqrt (‖v‖^2) := by
  let Eu := fun k => HeatMixedCellBound.energy F μ H
    (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k) u
  let Ev := fun k => HeatMixedCellBound.energy F μ H
    (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k) v
  have he (k : ℕ) (hk : k∈Finset.Icc 1 (ApproximationCells.index n H)) :
      |mixed F μ H S hS hcontr M I u v n k|≤
        Real.sqrt (HeatDualityGrid.width n:ℝ)*(Real.sqrt (Eu k)*Real.sqrt (Ev k)) := by
    have hk1 := (Finset.mem_Icc.mp hk).1
    let a := HeatDualityGrid.point H n (k-1)
    let b := HeatDualityGrid.point H n k
    have hab : a≤b := HeatDualityGrid.monotone H n (Nat.sub_le k 1)
    have hbH : b≤H := min_le_right _ _
    have hs : b-a≤HeatDualityGrid.width n := by
      have hh := HeatDualityGrid.size H n (k-1)
      simpa only [Nat.sub_add_cancel hk1] using hh
    have hsR : (b:ℝ)-(a:ℝ)≤(HeatDualityGrid.width n:ℝ) := by
      rw [←NNReal.coe_sub hab]
      exact_mod_cast hs
    have hh := HeatMixedCellBound.bound F μ H S hS hcontr M hM I hab hbH
      (HeatDualityGrid.width n-(b-a)) u v
    change |mixed F μ H S hS hcontr M I u v n k|≤Real.sqrt ((b:ℝ)-(a:ℝ))*Real.sqrt (Eu k)*Real.sqrt (Ev k) at hh
    exact hh.trans (by
      have hb := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsR)
        (mul_nonneg (Real.sqrt_nonneg (Eu k)) (Real.sqrt_nonneg (Ev k)))
      simpa only [mul_assoc] using hb)
  have hh := HeatDualityRemainder.sum_bound (Finset.Icc 1 (ApproximationCells.index n H))
    (HeatDualityGrid.width n:ℝ) Eu Ev (mixed F μ H S hS hcontr M I u v n)
    (fun k => HeatMixedCellBound.energy_nonneg F μ H _ _ u)
    (fun k => HeatMixedCellBound.energy_nonneg F μ H _ _ v) he
  change _≤Real.sqrt (HeatDualityGrid.width n:ℝ)*
    Real.sqrt (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),HeatMixedCellBound.energy F μ H
      (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k) u)*
    Real.sqrt (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),HeatMixedCellBound.energy F μ H
      (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k) v) at hh
  rw [sum_energy F μ H n u,sum_energy F μ H n v] at hh
  exact hh

theorem mixed_tends_zero (hM : ‖M‖≤1) (u v : Process (E := E) F μ H) :
    Tendsto (fun n => ∑ k∈Finset.Icc 1 (ApproximationCells.index n H),mixed F μ H S hS hcontr M I u v n k)
      atTop (𝓝 0) := by
  exact HeatDualityRemainder.tends_zero (fun n => (HeatDualityGrid.width n:ℝ)) _
    ApproximationClock.delta_tendsto (‖u‖^2) (‖v‖^2) (mixed_bound F μ H S hS hcontr M I hM u v)

end HeatPartitionEnergy
#check @HeatPartitionEnergy.sum_energy
#print axioms HeatPartitionEnergy.sum_energy
#check @HeatPartitionEnergy.mixed_bound
#print axioms HeatPartitionEnergy.mixed_bound
#check @HeatPartitionEnergy.mixed_tends_zero
#print HeatPartitionEnergy.mixed_tends_zero
#print axioms HeatPartitionEnergy.mixed_tends_zero
