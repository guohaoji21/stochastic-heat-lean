import HeatLocalBackwardEquation
import HeatPredictableDriftLinear
import HeatPredictableObservation
import SHE.TwoChannelItoRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatBackwardSolutionLinear

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open HeatBackwardDriver (state)
open HeatPredictableDriftLinear (drift_add drift_smul)
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

theorem state_add (t b : ℝ≥0) (η ξ : Lp E 2 μ) (f g : Process (E := E) F μ H) :
    state b (η + ξ) (f + g) t = state b η f t + state b ξ g t := by
  unfold state
  rw [drift_add, add_add_add_comm η ξ]
  exact congrArg Subtype.val (map_add (condExpL2 E ℝ (F.le t))
    (η + HeatPredictableDriftCell.value t b f) (ξ + HeatPredictableDriftCell.value t b g))

theorem state_smul (t b : ℝ≥0) (c : ℝ) (η : Lp E 2 μ) (f : Process (E := E) F μ H) :
    state b (c • η) (c • f) t = c • state b η f t := by
  unfold state
  rw [drift_smul, ← smul_add]
  exact congrArg Subtype.val (map_smul (condExpL2 E ℝ (F.le t)) c
    (η + HeatPredictableDriftCell.value t b f))

variable {J : StandardTerminalIto (C := E) (E := E) F μ H}
  {A M : E →L[ℝ] E} {a b : ℝ≥0} {η ξ : Lp E 2 μ}

/-- Superposition of actual backward solutions with the same operators. -/
def add (X : HeatLocalBackwardEquation.Solution J A M a b η)
    (Y : HeatLocalBackwardEquation.Solution J A M a b ξ) :
    HeatLocalBackwardEquation.Solution J A M a b (η + ξ) where
  drift := X.drift + Y.drift
  noise := X.noise + Y.noise
  predictableState := X.predictableState + Y.predictableState
  state_slices := by
    filter_upwards [X.state_slices, Y.state_slices, Measure.ae_ae_of_ae_prod
      (ae_eq_of_ae_eq_trim (Lp.coeFn_add X.predictableState Y.predictableState))]
      with t hx hy hsum
    by_cases ht : t ∈ Ioc a b
    · rw [indicator_of_mem ht] at hx hy ⊢
      rw [state_add]
      filter_upwards [hx, hy, hsum, Lp.coeFn_add (state b η X.drift t) (state b ξ Y.drift t)]
        with ω hx hy hsum hst
      rw [hsum, hst, Pi.add_apply, Pi.add_apply, hx, hy]
    · rw [indicator_of_notMem ht] at hx hy ⊢
      filter_upwards [hx, hy, hsum] with ω hx hy hsum
      simp only [hsum, Pi.add_apply, hx, hy, Pi.zero_apply, add_zero]
  drift_eq := by
    let L := HeatPredictableObservation.lift F μ H A
    let R := HeatPredictableObservation.lift F μ H M
    change _ = L (X.predictableState + Y.predictableState) + R (X.noise + Y.noise)
    rw [map_add, map_add]
    rw [show X.drift = L X.predictableState + R X.noise from X.drift_eq,
      show Y.drift = L Y.predictableState + R Y.noise from Y.drift_eq]
    abel
  noise_before := by rw [TwoChannelItoRows.stop_add, X.noise_before, Y.noise_before, add_zero]
  noise_after := by rw [TwoChannelItoRows.stop_add, X.noise_after, Y.noise_after]
  endpoint := by rw [state_add, X.endpoint, Y.endpoint]
  equation t hat htb := by
    rw [state_add, X.equation t hat htb, Y.equation t hat htb, drift_add,
      PastItoAlgebra.post_add, map_add]
    abel

/-- Scalar multiplication of the actual backward solution and all of its
predictable representatives. -/
def smul (c : ℝ) (X : HeatLocalBackwardEquation.Solution J A M a b η) :
    HeatLocalBackwardEquation.Solution J A M a b (c • η) where
  drift := c • X.drift
  noise := c • X.noise
  predictableState := c • X.predictableState
  state_slices := by
    filter_upwards [X.state_slices, Measure.ae_ae_of_ae_prod
      (ae_eq_of_ae_eq_trim (Lp.coeFn_smul c X.predictableState))] with t hx hs
    by_cases ht : t ∈ Ioc a b
    · rw [indicator_of_mem ht] at hx ⊢
      rw [state_smul]
      filter_upwards [hx, hs, Lp.coeFn_smul c (state b η X.drift t)] with ω hx hs hst
      rw [hs, hst, Pi.smul_apply, Pi.smul_apply, hx]
    · rw [indicator_of_notMem ht] at hx ⊢
      filter_upwards [hx, hs] with ω hx hs
      rw [hs, Pi.smul_apply, hx]
      exact smul_zero c
  drift_eq := by
    let L := HeatPredictableObservation.lift F μ H A
    let R := HeatPredictableObservation.lift F μ H M
    change _ = L (c • X.predictableState) + R (c • X.noise)
    rw [map_smul, map_smul, ← smul_add]
    exact congrArg (c • ·) X.drift_eq
  noise_before := by rw [StoppedInputAlgebra.stop_smul, X.noise_before, smul_zero]
  noise_after := by rw [StoppedInputAlgebra.stop_smul, X.noise_after]
  endpoint := by rw [state_smul, X.endpoint]
  equation t hat htb := by
    rw [state_smul, X.equation t hat htb, drift_smul, PastItoAlgebra.post_smul,
      map_smul, smul_sub, smul_add]

end HeatBackwardSolutionLinear

#print axioms HeatBackwardSolutionLinear.add
#print axioms HeatBackwardSolutionLinear.smul
