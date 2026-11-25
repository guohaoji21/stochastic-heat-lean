import HeatModalWeakMaximum
import HeatModalEnergySummation
import HeatModalControlEnergy

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatWeakForwardMaximum
open MeasureTheory Filter SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatFourierFrame
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

theorem integrable_maximum (hlocal : SHE.StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ) :
    Integrable (fun ω => HeatPathMaximum.value H sol.path ω^2) μ := by
  choose D hD hD0 hDe hbound using HeatModalWeakMaximum.exists_envelope F μ H M basis J U hU hE g sol hlocal hversions hnull
  let f := HeatControlAdapted.clamp U H
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm : MemLp f 2 (energyMeasure μ H) := HeatClampedControl.square_integrable F μ H U hU hE
  let C := HeatModalControlEnergy.bound H f
  have hC : ∀ n, MemLp (C n) 2 μ := HeatModalControlEnergy.square_integrable μ H f hfm
  have hCf := HeatModalControlEnergy.finite μ H f hf hfm
  let h := HeatWeakStochasticInput.noise F μ H M sol.input
  have hDf : (∑' n : ℤ,∫⁻ ω,ENNReal.ofReal ((D n ω)^2) ∂μ)<∞ := by
    have he (n : ℤ) : (∫⁻ ω,ENNReal.ofReal ((D n ω)^2) ∂μ)≤
        4*ENNReal.ofReal (‖HeatHilbertRandomStop.project F μ H (coordinate n) h‖^2) := by
      rw [←ofReal_integral_eq_lintegral_ofReal (hD n).integrable_sq
        (Eventually.of_forall (fun _ => sq_nonneg _))]
      have hn := ENNReal.ofReal_le_ofReal (hDe n)
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_ofNat] using hn
    have hs := ENNReal.tsum_le_tsum he
    rw [ENNReal.tsum_mul_left,HeatFourierFrameMeasure.projected_parseval F μ H h] at hs
    exact hs.trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
  exact HeatModalEnergySummation.integrable_maximum μ H sol.path sol.path_continuous
    (fun t => (sol.path_adapted t).measurable.mono (F.le t) le_rfl) g C D hC hD hCf hDf hbound

end HeatWeakForwardMaximum
#check @HeatWeakForwardMaximum.integrable_maximum
#print HeatWeakForwardMaximum.integrable_maximum
#print axioms HeatWeakForwardMaximum.integrable_maximum
