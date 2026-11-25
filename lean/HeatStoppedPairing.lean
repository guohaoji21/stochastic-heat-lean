import HeatPastPairing
import SHE.StoppedInputResolvent

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatStoppedPairing
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

def value (u : Process (E := E) F μ H) (t : ℝ≥0) : Lp E 2 μ :=
  I.integral (StoppedItoInputs.stop F μ H t u)

theorem value_integrable (u : Process (E := E) F μ H) :
    Integrable (value F μ H I u) (timeMeasure H) := by
  apply (integrable_const ‖u‖).mono'
  · exact (I.integral.continuous.comp_stronglyMeasurable
      (StoppedInputParameter.stronglyMeasurable F μ H u)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      change ‖I.integral (StoppedItoInputs.stop F μ H t u)‖≤‖u‖
      rw [I.integral.norm_map]
      exact StoppedInputResolvent.stop_norm_le F μ H u t)

theorem past_pairing (hl : StandardTerminalPastLocality I) (u : Process (E := E) F μ H)
    {t : ℝ≥0} (ht : t≤H) (Y : Lp E 2 μ) (hY : AEStronglyMeasurable[F t] Y μ) :
    inner ℝ Y (value F μ H I u H)=inner ℝ Y (value F μ H I u t) := by
  have hz := HeatPastPairing.future_orthogonal I hl t (StoppedItoInputs.stop F μ H H u) Y hY
  rw [PastItoAlgebra.post_stop_eq_sub F μ H t H ht u,map_sub,inner_sub_left] at hz
  change inner ℝ Y (I.integral (StoppedItoInputs.stop F μ H H u))=
    inner ℝ Y (I.integral (StoppedItoInputs.stop F μ H t u))
  calc
    _ = inner ℝ (I.integral (StoppedItoInputs.stop F μ H H u)) Y := real_inner_comm _ _
    _ = inner ℝ (I.integral (StoppedItoInputs.stop F μ H t u)) Y := sub_eq_zero.mp hz
    _ = _ := real_inner_comm _ _

theorem drift_pairing (hl : StandardTerminalPastLocality I) (u : Process (E := E) F μ H)
    (f : ℝ≥0 → Lp E 2 μ) (hf : Integrable f (timeMeasure H))
    (ha : ∀ᵐ t ∂timeMeasure H, AEStronglyMeasurable[F t] (f t) μ) :
    inner ℝ (∫ t,f t ∂timeMeasure H) (value F μ H I u H)=
      ∫ t,inner ℝ (f t) (value F μ H I u t) ∂timeMeasure H := by
  calc
    _ = ∫ t,inner ℝ (f t) (value F μ H I u H) ∂timeMeasure H := by
      rw [real_inner_comm,← integral_inner hf]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => real_inner_comm _ _)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ha,timeMeasure_ae_mem H] with t ht hb
      exact past_pairing F μ H I hl u hb.2 (f t) ht

end HeatStoppedPairing
#check @HeatStoppedPairing.value_integrable
#print axioms HeatStoppedPairing.value_integrable
#check @HeatStoppedPairing.past_pairing
#print axioms HeatStoppedPairing.past_pairing
#check @HeatStoppedPairing.drift_pairing
#print axioms HeatStoppedPairing.drift_pairing
