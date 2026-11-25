import HeatTerminalNaturality
import SHEStochastic.DirectHilbertBDG

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatTerminalBDG
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "νp" => (energyMeasure μ H).trim (predictable_le_product F)

theorem transfer (p : ℕ) (B : ℝ≥0)
    (hB : StandardTerminalBDGPower p (SHEStochastic.HilbertTerminalIto.terminalIto F μ H basis J) B) :
    StandardTerminalBDGPower p (HeatTerminalNaturality.integral F μ H basis J) B := by
  intro u
  let v : Process (E := Space Unit E) F μ H := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact HeatUnitHilbertLp.lpEquiv νp u
  have hva : v =ᵐ[energyMeasure μ H] (fun p => HeatUnitHilbertColumns.columnEquiv (u p)) := by
    have hvtrim : letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
        v =ᵐ[νp] (fun p => HeatUnitHilbertColumns.columnEquiv (u p)) := by
      letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      exact HeatUnitHilbertLp.lpEquiv_ae νp u
    exact ae_eq_of_ae_eq_trim hvtrim
  have he : ∀ᵐ p ∂energyMeasure μ H,
      ‖v p‖=‖u p‖ := by
    filter_upwards [hva] with p hp
    rw [hp]
    exact HeatUnitHilbertColumns.columnEquiv.norm_map _
  have hs := (Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae he
  have hbr : (fun ω => ∫⁻ s, ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure H) =ᵐ[μ]
      (fun ω => ∫⁻ s, ENNReal.ofReal (‖u (s,ω)‖^2) ∂timeMeasure H) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
    apply lintegral_congr_ae
    filter_upwards [hω] with s hs
    dsimp only [Prod.swap] at hs
    rw [hs]
  have hh := hB (v)
  have heq : (∫⁻ ω, (∫⁻ s, ENNReal.ofReal (‖v (s,ω)‖^2) ∂timeMeasure H)^p ∂μ) =
      ∫⁻ ω, (∫⁻ s, ENNReal.ofReal (‖u (s,ω)‖^2) ∂timeMeasure H)^p ∂μ :=
    lintegral_congr_ae (hbr.fun_comp (fun a => a^p))
  rw [heq] at hh
  exact hh

end HeatTerminalBDG
#check @HeatTerminalBDG.transfer
#print axioms HeatTerminalBDG.transfer
