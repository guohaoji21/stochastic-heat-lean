import HeatWeakEnergyIto
import HeatItoNormEnergyAt
import SHE.StoppedDampingClock

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatWeakEnergyDifference
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatDirichletResolvent HeatWeakEnergyEquation
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
  (s₁ s₂ : HeatWeakEnergyModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

def value (t : ℝ≥0) : Lp Base 2 μ := s₁.value t-s₂.value t

def drift (a : ℝ) (ha : 1 ≤ a) (t : ℝ≥0) : Lp Base 2 μ :=
  ((derivative a ha).compLpL 2 μ) (value F μ H M basis J U hU hE g s₁ s₂ t)

def noise (a : ℝ) (ha : 1 ≤ a) : Process (E := Base) F μ H :=
  HeatWeakEnergyProcess.noise F μ H M basis J U hU hE g s₁ a ha-
    HeatWeakEnergyProcess.noise F μ H M basis J U hU hE g s₂ a ha

theorem drift_difference {a : ℝ} (ha : 1 ≤ a) (t : ℝ≥0) :
    drift F μ H M basis J U hU hE g s₁ s₂ a ha t=
      HeatWeakEnergyProcess.drift F μ H M basis J U hU hE g s₁ a ha t-
        HeatWeakEnergyProcess.drift F μ H M basis J U hU hE g s₂ a ha t := by
  dsimp only [drift,value,HeatWeakEnergyProcess.drift]
  rw [map_sub]
  abel

theorem drift_integrable {a : ℝ} (ha : 1 ≤ a) :
    Integrable (drift F μ H M basis J U hU hE g s₁ s₂ a ha) (timeMeasure H) :=
  HeatCompactTimeIntegrability.of_continuous _
    (((derivative a ha).compLpL 2 μ).continuous.comp (s₁.mean_square_continuous.sub s₂.mean_square_continuous)) H

theorem drift_adapted {a : ℝ} (ha : 1 ≤ a) (t : ℝ≥0) :
    AEStronglyMeasurable[F t] (drift F μ H M basis J U hU hE g s₁ s₂ a ha t) μ := by
  have h1 := HeatWeakEnergyIto.drift_adapted F μ H M basis J U hU hE g s₁ ha t
  have h2 := HeatWeakEnergyIto.drift_adapted F μ H M basis J U hU hE g s₂ ha t
  rw [drift_difference]
  exact (h1.sub h2).congr (Lp.coeFn_sub _ _).symm

theorem representation {a : ℝ} (ha : 1 ≤ a) {T : ℝ≥0} (hT : T ≤ H) :
    ((smoothing a ha).compLpL 2 μ) (value F μ H M basis J U hU hE g s₁ s₂ T)=
      HeatDeterministicPairing.cumulative (timeMeasure H) (drift F μ H M basis J U hU hE g s₁ s₂ a ha) T+
      HeatStoppedPairing.value F μ H I (noise F μ H M basis J U hU hE g s₁ s₂ a ha) T := by
  let f₁ := HeatWeakEnergyProcess.drift F μ H M basis J U hU hE g s₁ a ha
  let f₂ := HeatWeakEnergyProcess.drift F μ H M basis J U hU hE g s₂ a ha
  let n₁ := HeatWeakEnergyProcess.noise F μ H M basis J U hU hE g s₁ a ha
  let n₂ := HeatWeakEnergyProcess.noise F μ H M basis J U hU hE g s₂ a ha
  have h₁ := HeatWeakEnergyProcess.representation F μ H M basis J U hU hE g s₁ ha hT
  have h₂ := HeatWeakEnergyProcess.representation F μ H M basis J U hU hE g s₂ ha hT
  have hc : HeatDeterministicPairing.cumulative (timeMeasure H)
      (drift F μ H M basis J U hU hE g s₁ s₂ a ha) T=
        HeatDeterministicPairing.cumulative (timeMeasure H) f₁ T-
          HeatDeterministicPairing.cumulative (timeMeasure H) f₂ T := by
    unfold HeatDeterministicPairing.cumulative
    rw [←integral_sub
      (HeatWeakEnergyProcess.drift_integrable F μ H M basis J U hU hE g s₁ ha H le_rfl).integrableOn
      (HeatWeakEnergyProcess.drift_integrable F μ H M basis J U hU hE g s₂ ha H le_rfl).integrableOn]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => drift_difference F μ H M basis J U hU hE g s₁ s₂ ha t)
  have hn : HeatStoppedPairing.value F μ H I (noise F μ H M basis J U hU hE g s₁ s₂ a ha) T=
      HeatStoppedPairing.value F μ H I n₁ T-HeatStoppedPairing.value F μ H I n₂ T := by
    dsimp only [HeatStoppedPairing.value,noise]
    rw [StoppedDampingClock.stop_sub,map_sub]
  change ((smoothing a ha).compLpL 2 μ) (s₁.value T-s₂.value T)=_
  rw [map_sub,h₁,h₂,hc,hn]
  abel

theorem energy (hlocal : StandardTerminalPastLocality J) {a : ℝ} (ha : 1 ≤ a) {T : ℝ≥0} (hT : T ≤ H) :
    ‖((smoothing a ha).compLpL 2 μ) (value F μ H M basis J U hU hE g s₁ s₂ T)‖^2=
      2*(∫ t,inner ℝ (drift F μ H M basis J U hU hE g s₁ s₂ a ha t)
        (((smoothing a ha).compLpL 2 μ) (value F μ H M basis J U hU hE g s₁ s₂ t)) ∂timeMeasure T)+
      ‖StoppedItoInputs.stop F μ H T (noise F μ H M basis J U hU hE g s₁ s₂ a ha)‖^2 := by
  have h0 : AEStronglyMeasurable[F 0] (0 : Lp Base 2 μ) μ :=
    stronglyMeasurable_const.aestronglyMeasurable.congr (Lp.coeFn_zero Base 2 μ).symm
  have he := HeatItoNormEnergyAt.energy F μ H I (HeatTerminalNaturality.locality F μ H basis J hlocal)
    0 h0 (drift F μ H M basis J U hU hE g s₁ s₂ a ha)
    (drift_integrable F μ H M basis J U hU hE g s₁ s₂ ha)
    (Eventually.of_forall (drift_adapted F μ H M basis J U hU hE g s₁ s₂ ha))
    (noise F μ H M basis J U hU hE g s₁ s₂ a ha)
    (fun t => ((smoothing a ha).compLpL 2 μ) (value F μ H M basis J U hU hE g s₁ s₂ t))
    (fun t ht => by simpa only [zero_add] using representation F μ H M basis J U hU hE g s₁ s₂ ha ht) hT
  simpa only [norm_zero,zero_pow (by norm_num : 2≠0),sub_zero] using he

end HeatWeakEnergyDifference
#check @HeatWeakEnergyDifference.drift_difference
#print axioms HeatWeakEnergyDifference.drift_difference
#check @HeatWeakEnergyDifference.drift_integrable
#print axioms HeatWeakEnergyDifference.drift_integrable
#check @HeatWeakEnergyDifference.drift_adapted
#print axioms HeatWeakEnergyDifference.drift_adapted
#check @HeatWeakEnergyDifference.representation
#print axioms HeatWeakEnergyDifference.representation
#check @HeatWeakEnergyDifference.energy
#print axioms HeatWeakEnergyDifference.energy
