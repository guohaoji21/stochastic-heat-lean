import HeatActualCellEnergy
import HeatLiftedSemigroup

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatMixedCellBound
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)

def energy (a b : ℝ≥0) (u : Process (E := E) F μ H) : ℝ :=
  ∫ p, (Ioc a b).indicator (fun s => ‖u (s,p.2)‖^2) p.1 ∂energyMeasure μ H

theorem energy_nonneg (a b : ℝ≥0) (u : Process (E := E) F μ H) : 0≤energy F μ H a b u :=
  integral_nonneg (fun p => Set.indicator_nonneg (fun s _ => sq_nonneg _) p.1)

theorem bound (hM : ‖M‖≤1) (I : StandardTerminalIto (C := E) (E := E) F μ H)
    {a b : ℝ≥0} (hab : a≤b) (hbH : b≤H) (ρ : ℝ≥0) (u v : Process (E := E) F μ H) :
    |inner ℝ (((S ρ).compLpL 2 μ) (I.integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u)))
      (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v)|≤
      Real.sqrt ((b:ℝ)-(a:ℝ))*Real.sqrt (energy F μ H a b u)*Real.sqrt (energy F μ H a b v) := by
  let U := HeatMildKernelCross.forward F μ H S hS hcontr M a b u
  let D := HeatActualCellEnergy.drift F μ H S hS hcontr M a b v
  let Eu := energy F μ H a b u
  let Ev := energy F μ H a b v
  let δ : ℝ := (b:ℝ)-(a:ℝ)
  have hEu : 0≤Eu := energy_nonneg F μ H a b u
  have hEv : 0≤Ev := energy_nonneg F μ H a b v
  have hδ : 0≤δ := sub_nonneg.mpr (by exact_mod_cast hab)
  have hM2 : ‖M‖^2≤1 := by nlinarith [norm_nonneg M]
  have hU : ‖U‖^2≤Eu := by
    have hh := HeatActualCellEnergy.forward F μ H S hS hcontr M a b u
    change ‖U‖^2≤‖M‖^2*Eu at hh
    exact hh.trans (by nlinarith)
  have hD : ‖D‖^2≤δ*Ev := by
    have hh := HeatActualCellEnergy.drift_bound F μ H S hS hcontr M hab hbH v
    have hb := HeatActualCellEnergy.backward F μ H S hS hcontr M a b v
    change ‖D‖^2≤δ*‖HeatBackwardKernel.input F μ H S hS hcontr M a b v‖^2 at hh
    change ‖HeatBackwardKernel.input F μ H S hS hcontr M a b v‖^2≤‖M‖^2*Ev at hb
    exact hh.trans (mul_le_mul_of_nonneg_left (hb.trans (by nlinarith)) hδ)
  have hnU : ‖U‖≤Real.sqrt Eu := Real.le_sqrt_of_sq_le hU
  have hnD : ‖D‖≤Real.sqrt δ*Real.sqrt Ev := by
    have hh := Real.le_sqrt_of_sq_le hD
    rw [Real.sqrt_mul hδ] at hh
    exact hh
  have hCI : ‖((S ρ).compLpL 2 μ) (I.integral U)‖≤‖U‖ := by
    exact (HeatLiftedSemigroup.contraction μ S hcontr ρ (I.integral U)).trans_eq (I.integral.norm_map U)
  calc
    _ ≤ ‖((S ρ).compLpL 2 μ) (I.integral U)‖*‖D‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt Eu*(Real.sqrt δ*Real.sqrt Ev) :=
      mul_le_mul (hCI.trans hnU) hnD (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by ring

end HeatMixedCellBound
#check @HeatMixedCellBound.energy_nonneg
#print axioms HeatMixedCellBound.energy_nonneg
#check @HeatMixedCellBound.bound
#print HeatMixedCellBound.bound
#print axioms HeatMixedCellBound.bound
