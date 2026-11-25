import HeatRegularizedEnergy
import HeatRegularizedGradientPairing

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatUniformGradientEnergy
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

def constant : ℝ := ‖Lp.const 2 μ g‖^2+
  (∫ t,‖HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t‖^2 ∂timeMeasure H)+
  (∫ t,‖sol.value t‖^2 ∂timeMeasure H)+‖HeatWeakStochasticInput.noise F μ H M sol.input‖^2

theorem constant_nonnegative : 0≤constant F μ H M basis J U hU hE g sol := by
  unfold constant
  positivity

theorem control_bound {a : ℝ} (ha : 1≤a) :
    2*(∫ t,inner ℝ
      (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))
      (((smoothing a ha).compLpL 2 μ) (sol.value t)) ∂timeMeasure H)≤
      (∫ t,‖HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t‖^2 ∂timeMeasure H)+
      (∫ t,‖sol.value t‖^2 ∂timeMeasure H) := by
  have hf := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm := HeatClampedControl.square_integrable F μ H U hU hE
  have hctrl := (HeatTimeLpField.square_integrable μ _ hf H hfm).norm.integrable_sq
  have hval : Integrable (fun t => ‖sol.value t‖^2) (timeMeasure H) :=
    HeatCompactTimeIntegrability.of_continuous _ (sol.mean_square_continuous.norm.pow 2) H
  have hpair := HeatRegularizedGradientPairing.control_integrable F μ H M basis J U hU hE g sol ha
  have hb (t : ℝ≥0) : 2*inner ℝ
      (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))
      (((smoothing a ha).compLpL 2 μ) (sol.value t))≤
      ‖HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t‖^2+‖sol.value t‖^2 := by
    have h₁ := HeatRegularizedGradientPairing.lp_contraction μ ha (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t)
    have h₂ := HeatRegularizedGradientPairing.lp_contraction μ ha (sol.value t)
    have hi := (real_inner_le_norm
      (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))
      (((smoothing a ha).compLpL 2 μ) (sol.value t))).trans
        (mul_le_mul h₁ h₂ (norm_nonneg _) (norm_nonneg _))
    nlinarith [sq_nonneg (‖HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t‖-‖sol.value t‖)]
  have hi := integral_mono (hpair.const_mul 2) (hctrl.add hval) hb
  have hadd : (∫ t,‖HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t‖^2+‖sol.value t‖^2 ∂timeMeasure H)=
      (∫ t,‖HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t‖^2 ∂timeMeasure H)+
      (∫ t,‖sol.value t‖^2 ∂timeMeasure H) := integral_add hctrl hval
  rw [integral_const_mul] at hi
  change 2*(∫ t,inner ℝ
      (((smoothing a ha).compLpL 2 μ) (HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t))
      (((smoothing a ha).compLpL 2 μ) (sol.value t)) ∂timeMeasure H)≤
      (∫ t,‖HeatTimeLpField.value μ (HeatControlAdapted.clamp U H) t‖^2+‖sol.value t‖^2 ∂timeMeasure H) at hi
  exact hi.trans_eq hadd

theorem bound (hlocal : StandardTerminalPastLocality J) {a : ℝ} (ha : 1≤a) :
    2*‖HeatPredictableLinearMap.map F μ H (HeatResolventGradient.gradient a ha) sol.input‖^2≤
      constant F μ H M basis J U hU hE g sol := by
  have he := HeatRegularizedEnergy.energy_identity F μ H M basis J U hU hE g sol hlocal ha
  rw [HeatRegularizedGradientPairing.drift_pairing F μ H M basis J U hU hE g sol ha] at he
  have hc := control_bound F μ H M basis J U hU hE g sol ha
  have hn := (StoppedInputResolvent.stop_norm_le F μ H
    (HeatRegularizedProcess.noise F μ H M basis J U hU hE g sol a ha) H).trans
      (HeatPredictableLinearMap.contraction F μ H (smoothing a ha) (smoothing_contraction ha)
        (HeatWeakStochasticInput.noise F μ H M sol.input))
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h0 : ‖Lp.const 2 μ (smoothing a ha g)‖≤‖Lp.const 2 μ g‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_const 2 μ (smoothing a ha g),Lp.coeFn_const 2 μ g] with ω hs hg
    rw [hs,hg]
    exact smoothing_contraction ha g
  have h02 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  unfold constant
  nlinarith [sq_nonneg ‖((smoothing a ha).compLpL 2 μ) (sol.value H)‖]

end HeatUniformGradientEnergy
#check @HeatUniformGradientEnergy.constant_nonnegative
#print axioms HeatUniformGradientEnergy.constant_nonnegative
#check @HeatUniformGradientEnergy.control_bound
#print axioms HeatUniformGradientEnergy.control_bound
#check @HeatUniformGradientEnergy.bound
#print HeatUniformGradientEnergy.bound
#print axioms HeatUniformGradientEnergy.bound
