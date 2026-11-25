import HeatHilbertFutureCenter
import SHEStochastic.DoobL2Envelope
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatStoppedMartingale
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

theorem conditional_stopped (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hlocal : StandardTerminalPastLocality J) {s t : ℝ≥0} (hst : s ≤ t) (v : Process (E := C) F μ H) :
    μ[(J.integral (StoppedItoInputs.stop F μ H t v) : Ω → E) | F s] =ᵐ[μ]
      J.integral (StoppedItoInputs.stop F μ H s v) := by
  have ht := (Lp.memLp (J.integral (StoppedItoInputs.stop F μ H t v))).integrable one_le_two
  have hs := (Lp.memLp (J.integral (StoppedItoInputs.stop F μ H s v))).integrable one_le_two
  obtain ⟨Z,hZ,hrep⟩ := J.adapted s (StoppedItoInputs.stop F μ H s v) (StoppedItoInputs.stop_stopped F μ H s v)
  have hsm : AEStronglyMeasurable[F s] (J.integral (StoppedItoInputs.stop F μ H s v) : Ω → E) μ :=
    hZ.aestronglyMeasurable.congr hrep.symm
  have he := condExp_sub ht hs (F s)
  have hz := HeatHilbertFutureCenter.condExp_increment_zero J hlocal hst v
  have hc := condExp_of_aestronglyMeasurable' (F.le s) hsm hs
  filter_upwards [he,hz,hc] with ω he hz hc
  simp only [Pi.sub_apply] at he
  have hh : μ[(J.integral (StoppedItoInputs.stop F μ H t v) : Ω → E) | F s] ω -
      J.integral (StoppedItoInputs.stop F μ H s v) ω = 0 := by
    rw [←hc]
    exact he.symm.trans hz
  exact sub_eq_zero.mp hh

theorem version_martingale (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hlocal : StandardTerminalPastLocality J) (v : Process (E := C) F μ H)
    (U : ℝ≥0 → Ω → E) (hUa : StronglyAdapted F U)
    (hU : ∀ t, U t =ᵐ[μ] J.integral (StoppedItoInputs.stop F μ H t v)) : Martingale U F μ := by
  refine ⟨hUa,fun s t hst => ?_⟩
  exact (condExp_congr_ae (m := F s) (hU t)).trans ((conditional_stopped J hlocal hst v).trans (hU s).symm)

theorem exists_envelope (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hlocal : StandardTerminalPastLocality J) (v : Process (E := C) F μ H)
    (U : ℝ≥0 → Ω → E) (hUa : StronglyAdapted F U) (hc : ∀ ω, Continuous (fun t => U t ω))
    (hU : ∀ t, U t =ᵐ[μ] J.integral (StoppedItoInputs.stop F μ H t v)) :
    ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧
      (∀ t : ℝ≥0, t ≤ H → ∀ ω, ‖U t ω‖ ≤ D ω) ∧
      ∀ ω, ∃ t : ℝ≥0, t ≤ H ∧ D ω = ‖U t ω‖ := by
  have hm := version_martingale J hlocal v U hUa hU
  have ht : MemLp (U H) 2 μ := (Lp.memLp _).ae_eq (hU H).symm
  exact SHEStochastic.DoobL2Envelope.exists_envelope hm hc H ht

end HeatStoppedMartingale
#check @HeatStoppedMartingale.conditional_stopped
#print axioms HeatStoppedMartingale.conditional_stopped
#check @HeatStoppedMartingale.version_martingale
#print axioms HeatStoppedMartingale.version_martingale
#check @HeatStoppedMartingale.exists_envelope
#print axioms HeatStoppedMartingale.exists_envelope
