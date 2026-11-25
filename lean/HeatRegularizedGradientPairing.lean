import HeatRegularizedProcess
import HeatResolventGradient
import HeatSliceEnergy
import HeatCompactLpBound
import HeatBoundedPairing

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatRegularizedGradientPairing
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
variable (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

theorem lp_contraction {a : ℝ} (ha : 1≤a) (X : Lp Base 2 μ) :
    ‖((smoothing a ha).compLpL 2 μ) X‖≤‖X‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(smoothing a ha).coeFn_compLpL X] with ω hω
  rw [hω]
  exact smoothing_contraction ha _

theorem control_integrable {a : ℝ} (ha : 1≤a) :
    Integrable (fun t => inner ℝ
      (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))
      (((smoothing a ha).compLpL 2 μ) (sol.value t))) (timeMeasure H) := by
  let L := (smoothing a ha).compLpL 2 μ
  have hf := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm := HeatClampedControl.square_integrable F μ H U hU hE
  have hi := L.integrable_comp ((HeatTimeLpField.square_integrable μ _ hf H hfm).integrable (by norm_num : (1:ENNReal)≤2))
  obtain ⟨C,hC0,hC⟩ := HeatCompactLpBound.exists_bound μ H sol.value sol.mean_square_continuous
  apply HeatBoundedPairing.integrable (timeMeasure H) _ _ hi
    (L.continuous.comp sol.mean_square_continuous).aestronglyMeasurable C
  filter_upwards [timeMeasure_ae_mem H] with t ht
  exact (lp_contraction μ ha (sol.value t)).trans (hC t ht.2)

theorem drift_pairing {a : ℝ} (ha : 1≤a) :
    (∫ t,inner ℝ (HeatRegularizedProcess.drift F μ H M basis J U hU hE g sol a ha t)
      (((smoothing a ha).compLpL 2 μ) (sol.value t)) ∂timeMeasure H)=
      -‖HeatPredictableLinearMap.map F μ H (HeatResolventGradient.gradient a ha) sol.input‖^2+
      (∫ t,inner ℝ
        (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))
        (((smoothing a ha).compLpL 2 μ) (sol.value t)) ∂timeMeasure H) := by
  have hAi : Integrable (fun t => inner ℝ (((derivative a ha).compLpL 2 μ) (sol.value t))
      (((smoothing a ha).compLpL 2 μ) (sol.value t))) (timeMeasure H) :=
    HeatCompactTimeIntegrability.of_continuous _
      ((((derivative a ha).compLpL 2 μ).continuous.comp sol.mean_square_continuous).inner
        (((smoothing a ha).compLpL 2 μ).continuous.comp sol.mean_square_continuous)) H
  have hgrad : (∫ t,inner ℝ (((derivative a ha).compLpL 2 μ) (sol.value t))
      (((smoothing a ha).compLpL 2 μ) (sol.value t)) ∂timeMeasure H)=
      -‖HeatPredictableLinearMap.map F μ H (HeatResolventGradient.gradient a ha) sol.input‖^2 := by
    calc
      _ = ∫ t,-‖((HeatResolventGradient.gradient a ha).compLpL 2 μ) (sol.value t)‖^2 ∂timeMeasure H :=
        integral_congr_ae (Eventually.of_forall (fun t => HeatResolventGradient.lp_drift_energy μ ha (sol.value t)))
      _ = -(∫ t,‖((HeatResolventGradient.gradient a ha).compLpL 2 μ) (sol.value t)‖^2 ∂timeMeasure H) := integral_neg _
      _ = _ := congrArg Neg.neg (HeatSliceEnergy.energy F μ H sol.input sol.value sol.input_slices (HeatResolventGradient.gradient a ha))
  have he (t : ℝ≥0) : inner ℝ (HeatRegularizedProcess.drift F μ H M basis J U hU hE g sol a ha t)
      (((smoothing a ha).compLpL 2 μ) (sol.value t))=
      inner ℝ (((derivative a ha).compLpL 2 μ) (sol.value t)) (((smoothing a ha).compLpL 2 μ) (sol.value t))+
      inner ℝ (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))
        (((smoothing a ha).compLpL 2 μ) (sol.value t)) := inner_add_left _ _ _
  rw [integral_congr_ae (Eventually.of_forall he),integral_add hAi
    (control_integrable F μ H M basis J U hU hE g sol ha),hgrad]

end HeatRegularizedGradientPairing
#check @HeatRegularizedGradientPairing.lp_contraction
#print axioms HeatRegularizedGradientPairing.lp_contraction
#check @HeatRegularizedGradientPairing.control_integrable
#print axioms HeatRegularizedGradientPairing.control_integrable
#check @HeatRegularizedGradientPairing.drift_pairing
#print HeatRegularizedGradientPairing.drift_pairing
#print axioms HeatRegularizedGradientPairing.drift_pairing
