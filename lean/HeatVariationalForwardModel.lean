import HeatSobolevForwardModel
import HeatWeakForwardMaximum

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatVariationalForwardModel
open MeasureTheory SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatWeakDirichlet
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)

structure Solution extends HeatSobolevForwardModel.Solution F μ H M I U hU hE g where
  maximum_energy : Integrable (fun ω => HeatPathMaximum.value H weak.path ω^2) μ

end HeatVariationalForwardModel
namespace HeatVariationalForwardModel
open MeasureTheory SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatWeakDirichlet
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]

theorem exists_solution (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
    (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
    (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (hH : 0<H) (hlocal : SHE.StandardTerminalPastLocality J) (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : SHE.StandardTerminalBDGPower 8 (HeatTerminalNaturality.integral F μ H basis J) B)
    (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base) :
    Nonempty (Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g) := by
  obtain ⟨sol⟩ := HeatSobolevForwardModel.exists_solution F μ H M basis J hH hlocal hversions hnull B hB U hU hE g
  exact ⟨⟨sol,HeatWeakForwardMaximum.integrable_maximum F μ H M basis J U hU hE g sol.weak hlocal hversions hnull⟩⟩

end HeatVariationalForwardModel
#check @HeatVariationalForwardModel.exists_solution
#print HeatVariationalForwardModel.Solution
#print HeatVariationalForwardModel.exists_solution
#print axioms HeatVariationalForwardModel.exists_solution
