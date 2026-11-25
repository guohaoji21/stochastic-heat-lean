import HeatH01VariationalEquation

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatSobolevForwardModel
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatWeakDirichlet
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (I : StandardTerminalIto (C := Base) (E := Base) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)

structure Solution where
  weak : HeatWeakForwardModel.Solution F μ H M I U hU hE g
  sobolev : Process (E := H01) F μ H
  input_embedding : HeatResolventH01Compact.embedProcess F μ H sobolev=weak.input

end HeatSobolevForwardModel
namespace HeatSobolevForwardModel
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatWeakDirichlet
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]

theorem exists_solution (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
    (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (hH : 0<H) (hlocal : StandardTerminalPastLocality J) (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 (HeatTerminalNaturality.integral F μ H basis J) B)
    (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base) :
    Nonempty (Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g) := by
  obtain ⟨sol⟩ := HeatWeakForwardModel.exists_solution F μ H M basis J hH hlocal hversions hnull B hB U hU hE g
  obtain ⟨v,hv⟩ := HeatResolventH01Compact.exists_h01_input F μ H M basis J U hU hE g sol hlocal
  exact ⟨⟨sol,v,hv⟩⟩

end HeatSobolevForwardModel
#check @HeatSobolevForwardModel.exists_solution
#print HeatSobolevForwardModel.Solution
#print HeatSobolevForwardModel.exists_solution
#print axioms HeatSobolevForwardModel.exists_solution
