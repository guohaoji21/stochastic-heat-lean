import HeatTorusControlObservation
import HeatPredictableObservation
import HeatBackwardEquationEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace HeatTorusBackwardObservation

open Filter MeasureTheory Set SHE SHE.PredictableL2 UnitAddTorus
open HeatTorusGalerkinBackward (State)
open HeatTorusControlObservation (Control observe inject)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0} {S : Finset (ι → ℤ)}
  {J : StandardTerminalIto (C := State S) (E := State S) F μ H}
  {A M : State S →L[ℝ] State S} {η : Lp (State S) 2 μ}

def observation (O : Set (UnitAddTorus ι))
    (Y : HeatLocalBackwardEquation.Solution J A M 0 H η) : Process (E := Control O) F μ H :=
  HeatPredictableObservation.lift F μ H (observe S O) Y.predictableState

omit [Fintype ι] in
private theorem state_slices (Y : HeatLocalBackwardEquation.Solution J A M 0 H η) :
    ∀ᵐ t ∂timeMeasure H, (fun ω => Y.predictableState (t, ω)) =ᵐ[μ]
      HeatBackwardDriver.state H η Y.drift t := by
  filter_upwards [Y.state_slices, timeMeasure_ae_mem H] with t h ht
  rw [Set.indicator_of_mem ht] at h
  exact h

/-- The observation of the backward equation belongs to the actual
predictable local control space, with its spectral observation norm. -/
theorem energy (O : Set (UnitAddTorus ι))
    (Y : HeatLocalBackwardEquation.Solution J A M 0 H η) :
    ‖observation O Y‖ ^ 2 =
      ∫ t, HeatTorusObservedPolynomial.observedEnergy O
        (HeatBackwardDriver.state H η Y.drift t) ∂timeMeasure H := by
  have h := HeatPredictableObservation.energy F μ H (observation O Y)
    (fun t => ((observe S O).compLpL 2 μ) (HeatBackwardDriver.state H η Y.drift t))
    (HeatPredictableObservation.lift_slices F μ H (observe S O) Y.predictableState _
      (state_slices Y))
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall fun t =>
    HeatTorusControlObservation.observation_norm_sq S O (HeatBackwardDriver.state H η Y.drift t)

variable [IsSeparable μ]

/-- Pairing a predictable control with the backward observation equals
pairing its spatial injection with the finite backward state. -/
theorem pairing (O : Set (UnitAddTorus ι))
    (Y : HeatLocalBackwardEquation.Solution J A M 0 H η) (u : Process (E := Control O) F μ H) :
    inner ℝ u (observation O Y) =
      ∫ t, inner ℝ (HeatBackwardEquationEnergy.slice (HeatPredictableObservation.lift F μ H (inject S O) u) t)
        (HeatBackwardDriver.state H η Y.drift t) ∂timeMeasure H := by
  let f := HeatPredictableObservation.lift F μ H (inject S O) u
  have h := HeatPredictableObservation.lift_inner F μ H (inject S O) (observe S O)
    (HeatTorusControlObservation.inject_inner S O) u Y.predictableState
  change inner ℝ f Y.predictableState = inner ℝ u (observation O Y) at h
  rw [← h]
  exact HeatPredictableObservation.inner_slices F μ H f Y.predictableState
    (HeatBackwardEquationEnergy.slice f) (HeatBackwardDriver.state H η Y.drift)
    (HeatPredictableObservation.slice_ae F μ H f) (state_slices Y)

end HeatTorusBackwardObservation

#print axioms HeatTorusBackwardObservation.energy
#print axioms HeatTorusBackwardObservation.pairing
