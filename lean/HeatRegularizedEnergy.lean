import HeatRegularizedProcess
import HeatItoNormEnergy
import HeatLpAdaptedMap

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatRegularizedEnergy
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatDirichletResolvent HeatRegularizedWeakEquation
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
variable (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

theorem drift_adapted {a : ℝ} (ha : 1≤a) (t : ℝ≥0) :
    AEStronglyMeasurable[F t] (HeatRegularizedProcess.drift F μ H M basis J U hU hE g sol a ha t) μ := by
  obtain ⟨Z,hZ,hVZ⟩ := sol.adapted_values t
  have hV : AEStronglyMeasurable[F t] (sol.value t) μ := hZ.aestronglyMeasurable.congr hVZ.symm
  have hf := (HeatControlAdapted.clamp_progressive F U hU H).stronglyAdapted
  have hctrl := HeatTimeLpDrift.adapted μ (HeatControlAdapted.clamp U H) F hf t
  exact ((HeatLpAdaptedMap.map F μ (derivative a ha) t (sol.value t) hV).add
    (HeatLpAdaptedMap.map F μ (smoothing a ha) t _ hctrl)).congr
      (Lp.coeFn_add (((derivative a ha).compLpL 2 μ) (sol.value t))
        (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))).symm

theorem energy_identity (hlocal : StandardTerminalPastLocality J) {a : ℝ} (ha : 1≤a) :
    ‖((smoothing a ha).compLpL 2 μ) (sol.value H)‖^2-‖Lp.const 2 μ (smoothing a ha g)‖^2=
      2*(∫ t,inner ℝ (HeatRegularizedProcess.drift F μ H M basis J U hU hE g sol a ha t)
        (((smoothing a ha).compLpL 2 μ) (sol.value t)) ∂timeMeasure H)+
      ‖StoppedItoInputs.stop F μ H H (HeatRegularizedProcess.noise F μ H M basis J U hU hE g sol a ha)‖^2 := by
  have h0 : AEStronglyMeasurable[F 0] (Lp.const 2 μ (smoothing a ha g) : Lp Base 2 μ) μ :=
    stronglyMeasurable_const.aestronglyMeasurable.congr (Lp.coeFn_const 2 μ (smoothing a ha g)).symm
  exact HeatItoNormEnergy.energy F μ H (I) (HeatTerminalNaturality.locality F μ H basis J hlocal)
    (Lp.const 2 μ (smoothing a ha g)) h0
    (HeatRegularizedProcess.drift F μ H M basis J U hU hE g sol a ha)
    (HeatRegularizedProcess.drift_integrable F μ H M basis J U hU hE g sol ha H le_rfl)
    (Eventually.of_forall (drift_adapted F μ H M basis J U hU hE g sol ha))
    (HeatRegularizedProcess.noise F μ H M basis J U hU hE g sol a ha)
    (fun t => ((smoothing a ha).compLpL 2 μ) (sol.value t))
    (fun t ht => HeatRegularizedProcess.representation F μ H M basis J U hU hE g sol ha ht)

end HeatRegularizedEnergy
#check @HeatRegularizedEnergy.drift_adapted
#print axioms HeatRegularizedEnergy.drift_adapted
#check @HeatRegularizedEnergy.energy_identity
#print HeatRegularizedEnergy.energy_identity
#print axioms HeatRegularizedEnergy.energy_identity
