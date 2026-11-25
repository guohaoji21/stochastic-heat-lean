import HeatLpSpatialExt
import SHE.StoppedInputParameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1350000
noncomputable section

namespace HeatTerminalCrossNaturality

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω E V κ ℓ : Type*} [mΩ : MeasurableSpace Ω] [Countable κ] [Countable ℓ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

local notation "ν" => Measure.trim (energyMeasure μ H) (predictable_le_product F)

/-- A bounded map between different state spaces commutes with the Hilbert
integrals built from the same scalar Brownian integral. -/
theorem commutes (b : HilbertBasis κ ℝ E) (c : HilbertBasis ℓ ℝ V)
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (A : E →L[ℝ] V) (u : Process (E := E) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    (A.compLpL 2 μ) ((HeatTerminalNaturality.integral F μ H b J).integral u) =
      (HeatTerminalNaturality.integral F μ H c J).integral ((A.compLpL 2 ν) u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply HeatLpSpatialExt.ext μ
  intro v
  rw [HeatTerminalNaturality.compLp_comp μ,
    HeatTerminalNaturality.scalar_commutes F μ H b J,
    HeatTerminalNaturality.scalar_commutes F μ H c J,
    HeatTerminalNaturality.compLp_comp ν]

theorem map_stop (A : E →L[ℝ] V) (t : ℝ≥0) (u : Process (E := E) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    (A.compLpL 2 ν) (stop F μ H t u) = stop F μ H t ((A.compLpL 2 ν) u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim (A.coeFn_compLpL (stop F μ H t u)),
    ae_eq_of_ae_eq_trim (A.coeFn_compLpL u), stop_ae F μ H t u,
    stop_ae F μ H t ((A.compLpL 2 ν) u)] with p h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₄]
  by_cases hp : p ∈ before (t : ℝ)
  · rw [indicator_of_mem hp, indicator_of_mem hp, h₂]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp, map_zero]

theorem stopped_commutes (b : HilbertBasis κ ℝ E) (c : HilbertBasis ℓ ℝ V)
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (A : E →L[ℝ] V) (t : ℝ≥0) (u : Process (E := E) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    (A.compLpL 2 μ) ((HeatTerminalNaturality.integral F μ H b J).integral (stop F μ H t u)) =
      (HeatTerminalNaturality.integral F μ H c J).integral (stop F μ H t ((A.compLpL 2 ν) u)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [commutes F μ H b c J, map_stop F μ H]

end HeatTerminalCrossNaturality

#print axioms HeatTerminalCrossNaturality.commutes
#print axioms HeatTerminalCrossNaturality.stopped_commutes
