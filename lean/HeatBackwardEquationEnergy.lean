import HeatLocalBackwardEquation
import HeatBackwardCellSupport
import HeatTimeLpDrift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1450000
noncomputable section

namespace HeatBackwardEquationEnergy

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open HeatBackwardDriver (state)
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

variable {J : StandardTerminalIto (C := E) (E := E) F μ H}
  {A B : E →L[ℝ] E} {η : Lp E 2 μ}

/-- The backward integral equation rewritten from time zero using the
same predictable integrand and the same terminal Itô map. -/
theorem forward_form (S : HeatLocalBackwardEquation.Solution J A B 0 H η) {t : ℝ≥0} (ht : t ≤ H) :
    state H η S.drift t = state H η S.drift 0 - HeatPredictableDriftCell.value 0 t S.drift +
      J.integral (stop F μ H t S.noise) := by
  have h0 := S.equation 0 le_rfl (show (0 : ℝ≥0) ≤ H from bot_le)
  have hsupport := HeatBackwardCellSupport.of_stops S.noise_before S.noise_after
  rw [HeatBackwardCellSupport.post_eq_of_le le_rfl hsupport,
    HeatPredictableDriftCell.split (show (0 : ℝ≥0) ≤ t from bot_le) ht S.drift] at h0
  have hpost := PastItoAlgebra.post_stop_eq_sub F μ H t H ht S.noise
  rw [S.noise_after] at hpost
  rw [S.equation t (show (0 : ℝ≥0) ≤ t from bot_le) ht, hpost, map_sub, h0]
  abel

section Slices

variable [IsSeparable μ]

private theorem measurable_process (u : Process (E := E) F μ H) :
    Measurable (u : ℝ≥0 × Ω → E) :=
  ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable

private theorem ambient_memLp (u : Process (E := E) F μ H) :
    MemLp (u : ℝ≥0 × Ω → E) 2 (energyMeasure μ H) :=
  memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)

def slice (u : Process (E := E) F μ H) (t : ℝ≥0) : Lp E 2 μ :=
  HeatTimeLpField.value μ u t

/-- The predictable driver really is the sum of the two operators on the
state and noise slices appearing in the expected energy identity. -/
theorem drift_slices (S : HeatLocalBackwardEquation.Solution J A B 0 H η) :
    ∀ᵐ t ∂timeMeasure H, slice S.drift t =
      (A.compLpL 2 μ) (state H η S.drift t) + (B.compLpL 2 μ) (slice S.noise t) := by
  let U := HeatPredictableLinearMap.map F μ H A S.predictableState
  let V := HeatPredictableLinearMap.map F μ H B S.noise
  have hsum : (S.drift : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] (U : ℝ≥0 × Ω → E) + V := by
    have he : S.drift = U + V := S.drift_eq
    rw [he]
    exact ae_eq_of_ae_eq_trim (Lp.coeFn_add U V)
  have hu := Measure.ae_ae_of_ae_prod (HeatPredictableLinearMap.map_ae F μ H A S.predictableState)
  have hv := Measure.ae_ae_of_ae_prod (HeatPredictableLinearMap.map_ae F μ H B S.noise)
  have hd := HeatTimeLpField.value_ae μ S.drift (measurable_process S.drift) H (ambient_memLp S.drift)
  have hz := HeatTimeLpField.value_ae μ S.noise (measurable_process S.noise) H (ambient_memLp S.noise)
  filter_upwards [S.state_slices, timeMeasure_ae_mem H, Measure.ae_ae_of_ae_prod hsum, hu, hv, hd, hz]
    with t hstate ht hsum hu hv hd hz
  rw [indicator_of_mem ht] at hstate
  apply Lp.ext
  filter_upwards [hstate, hsum, hu, hv, hd, hz,
    Lp.coeFn_add ((A.compLpL 2 μ) (state H η S.drift t)) ((B.compLpL 2 μ) (slice S.noise t)),
    A.coeFn_compLpL (state H η S.drift t), B.coeFn_compLpL (slice S.noise t)]
    with ω hstate hsum hu hv hd hz hadd ha hb
  change slice S.drift t ω = S.drift (t, ω) at hd
  change slice S.noise t ω = S.noise (t, ω) at hz
  change U (t, ω) = A (S.predictableState (t, ω)) at hu
  change V (t, ω) = B (S.noise (t, ω)) at hv
  rw [hd, hsum, Pi.add_apply, hu, hv, hstate, ← hz, hadd, Pi.add_apply, ha, hb]

theorem cumulative_eq (u : Process (E := E) F μ H) {t : ℝ≥0} (ht : t ≤ H) :
    HeatDeterministicPairing.cumulative (timeMeasure H) (slice u) t = HeatPredictableDriftCell.value 0 t u := by
  rw [show HeatDeterministicPairing.cumulative (timeMeasure H) (slice u) t =
      HeatAmbientDrift.value μ H u (measurable_process u) (ambient_memLp u) t from
    HeatTimeLpDrift.cumulative_value μ H u (measurable_process u) (ambient_memLp u) ht]
  have he : (fun ω => ∫ s, u (s, ω) ∂timeMeasure t) = HeatBochnerCell.value H u 0 t := by
    unfold HeatBochnerCell.value
    rw [timeMeasure_restrict_Ioc 0 ht]
    rfl
  apply Lp.ext
  exact ((HeatAmbientDrift.value_ae μ H u (measurable_process u) (ambient_memLp u) ht).trans
    (EventuallyEq.of_eq he)).trans (HeatPredictableDriftCell.value_ae 0 t u).symm

/-- Expected energy identity for the constructed backward equation, with
actual predictable drift and diffusion slices on each deterministic prefix. -/
theorem energy_prefix (hJ : StandardTerminalPastLocality J)
    (S : HeatLocalBackwardEquation.Solution J A B 0 H η) {t : ℝ≥0} (ht : t ≤ H) :
    ‖state H η S.drift t‖ ^ 2 - ‖state H η S.drift 0‖ ^ 2 =
      2 * (∫ s, inner ℝ (-slice S.drift s) (state H η S.drift s) ∂timeMeasure t) +
        ∫ s, ‖slice S.noise s‖ ^ 2 ∂timeMeasure t := by
  have hi : Integrable (fun s => -slice S.drift s) (timeMeasure H) :=
    ((HeatTimeLpField.square_integrable μ S.drift (measurable_process S.drift)
      H (ambient_memLp S.drift)).integrable one_le_two).neg
  have ha : ∀ᵐ s ∂timeMeasure H, AEStronglyMeasurable[F s] ((-slice S.drift s : Lp E 2 μ) : Ω → E) μ := by
    apply Eventually.of_forall
    intro s
    have hp : IsStronglyPredictable F (Function.curry (S.drift : ℝ≥0 × Ω → E)) :=
      Lp.stronglyMeasurable S.drift
    exact (HeatTimeLpDrift.adapted μ S.drift F (fun r => hp.stronglyAdapted r) s).neg.congr
      (Lp.coeFn_neg _).symm
  have hZ := (HeatTimeLpField.value_ae μ S.noise (measurable_process S.noise) H (ambient_memLp S.noise)).mono
    (fun _ h => h.symm)
  refine HeatTerminalItoCompression.energy_prefix J hJ ht _ (HeatBackwardDriver.state_adapted H η S.drift 0)
    (fun s => -slice S.drift s) hi ha S.noise (state H η S.drift) (slice S.noise) hZ ?_
  intro s hs
  have he : HeatDeterministicPairing.cumulative (timeMeasure H) (fun s => -slice S.drift s) s =
      -HeatPredictableDriftCell.value 0 s S.drift := by
    rw [← cumulative_eq S.drift hs]
    exact integral_neg _
  rw [he]
  simpa only [sub_eq_add_neg, HeatStoppedPairing.value] using forward_form S hs

end Slices

end HeatBackwardEquationEnergy

#print axioms HeatBackwardEquationEnergy.forward_form
#print axioms HeatBackwardEquationEnergy.drift_slices
#print axioms HeatBackwardEquationEnergy.energy_prefix
