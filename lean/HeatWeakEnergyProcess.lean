import HeatWeakEnergyEquation
import HeatTimeLpDrift
import HeatPredictableLinearMap
import HeatStoppedPairing

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatWeakEnergyProcess
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatDirichletResolvent HeatWeakEnergyEquation
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
  (sol : HeatWeakEnergyModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

def drift (a : ℝ) (ha : 1≤a) (t : ℝ≥0) : Lp Base 2 μ :=
  ((derivative a ha).compLpL 2 μ) (sol.value t)+
    ((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t)

def noise (a : ℝ) (ha : 1≤a) : Process (E := Base) F μ H :=
  HeatPredictableLinearMap.map F μ H (smoothing a ha) (HeatWeakStochasticInput.noise F μ H M sol.input)

theorem drift_integrable {a : ℝ} (ha : 1≤a) (T : ℝ≥0) (hT : T≤H) :
    Integrable (drift F μ H M basis J U hU hE g sol a ha) (timeMeasure T) := by
  have hfm := HeatClampedControl.square_integrable F μ H U hU hE
  have hf := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hmT : MemLp (HeatControlAdapted.clamp U H) 2 (energyMeasure μ T) :=
    hfm.mono_measure (Measure.prod_mono (HeatTimeRestriction.mono hT) le_rfl)
  exact (HeatCompactTimeIntegrability.of_continuous _
    (((derivative a ha).compLpL 2 μ).continuous.comp sol.mean_square_continuous) T).add
      (((smoothing a ha).compLpL 2 μ).integrable_comp
        ((HeatTimeLpField.square_integrable μ _ hf T hmT).integrable (by norm_num)))

theorem representation {a : ℝ} (ha : 1≤a) {T : ℝ≥0} (hT : T≤H) :
    ((smoothing a ha).compLpL 2 μ) (sol.value T)=Lp.const 2 μ (smoothing a ha g)+
      HeatDeterministicPairing.cumulative (timeMeasure H) (drift F μ H M basis J U hU hE g sol a ha) T+
      HeatStoppedPairing.value F μ H (I) (noise F μ H M basis J U hU hE g sol a ha) T := by
  let f := HeatControlAdapted.clamp U H
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm := HeatClampedControl.square_integrable F μ H U hU hE
  have hmT : MemLp f 2 (energyMeasure μ T) := hfm.mono_measure
    (Measure.prod_mono (HeatTimeRestriction.mono hT) le_rfl)
  have hfT := (HeatTimeLpField.square_integrable μ f hf T hmT).integrable (by norm_num : (1:ENNReal)≤2)
  have hA : Integrable (fun t => ((derivative a ha).compLpL 2 μ) (sol.value t)) (timeMeasure T) :=
    HeatCompactTimeIntegrability.of_continuous _
      (((derivative a ha).compLpL 2 μ).continuous.comp sol.mean_square_continuous) T
  have hc : HeatDeterministicPairing.cumulative (timeMeasure H) (drift F μ H M basis J U hU hE g sol a ha) T=
      (∫ t,((derivative a ha).compLpL 2 μ) (sol.value t) ∂timeMeasure T)+
        ((smoothing a ha).compLpL 2 μ) (HeatAmbientDrift.value μ H f hf hfm T) := by
    unfold HeatDeterministicPairing.cumulative
    rw [HeatTimeRestriction.restrict_Iio hT]
    change (∫ t,((derivative a ha).compLpL 2 μ) (sol.value t)+
      ((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ f t) ∂timeMeasure T)=_
    rw [integral_add hA (((smoothing a ha).compLpL 2 μ).integrable_comp hfT),
      ((smoothing a ha).compLpL 2 μ).integral_comp_comm hfT,
      HeatTimeLpDrift.integral_value μ H f hf hfm hT]
  have hn := HeatTerminalNaturality.commutes F μ H basis J (smoothing a ha)
    (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.input))
  change ((smoothing a ha).compLpL 2 μ) ((I).integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.input)))=
    (I).integral (HeatPredictableLinearMap.map F μ H (smoothing a ha)
      (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.input))) at hn
  rw [HeatPredictableLinearMap.stop_commutes] at hn
  have hw := HeatWeakEnergyEquation.equation F μ H M (I) U hU hE g sol ha hT
  rw [hc]
  dsimp only [HeatStoppedPairing.value,noise]
  rw [hn] at hw
  exact hw.trans (by abel)

end HeatWeakEnergyProcess
#check @HeatWeakEnergyProcess.drift_integrable
#print axioms HeatWeakEnergyProcess.drift_integrable
#check @HeatWeakEnergyProcess.representation
#print HeatWeakEnergyProcess.representation
#print axioms HeatWeakEnergyProcess.representation
