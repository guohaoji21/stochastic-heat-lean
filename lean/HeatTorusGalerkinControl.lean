import HeatTorusGalerkinObservability
import HeatTorusGalerkinTerminalDuality
import HeatTorusBackwardObservation
import HeatBackwardControlDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatTorusGalerkinControl

open MeasureTheory Filter SHE SHE.PredictableL2 UnitAddTorus
open HeatTorusGalerkinBackward (State laplace multiplier)
open HeatTorusControlObservation (Control observe inject)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

local notation "Ω" => C(ℝ≥0, ℝ)
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable
local instance : MeasurableSpace (HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (HilbertColumns.Space Unit ℝ) := ⟨rfl⟩

local notation "J" => fun H S => HeatTerminalNaturality.integral F μ H
  (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar H)

/-- One bound works for all finite Galerkin control problems. Each chosen
control makes the terminal state vanish in the corresponding additive
Itô equation with the given initial state, drift and diffusion. -/
theorem exists_null_control {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ)) (hb : ∀ x, (b x).im = 0)
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * HeatGevreyFourierExtension.weight k))
    {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty) {H : ℝ≥0} (hH : 0 < H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset (ι → ℤ)) (g : Lp (State S) 2 μ),
      ∃ u : Process (E := Control O) F μ H, ‖u‖ ≤ K * ‖g‖ ∧
        ∀ X : HeatItoProductEnergy.Trajectory (J H S),
          X.state 0 = g →
          AEStronglyMeasurable[F H] (X.state H : Ω → State S) μ →
          (∀ᵐ t ∂timeMeasure H, X.drift t = ((laplace S P).compLpL 2 μ) (X.state t) +
            HeatBackwardEquationEnergy.slice (HeatPredictableObservation.lift F μ H (inject S O) u) t) →
          (∀ᵐ t ∂timeMeasure H, X.noise t = ((multiplier S b).compLpL 2 μ) (X.state t)) →
          X.state H = 0 := by
  obtain ⟨L, hL, hobs⟩ := HeatTorusGalerkinObservability.observable hP hC ha b hdec hO hOne hH
  refine ⟨Real.sqrt L, Real.sqrt_nonneg _, fun S g => ?_⟩
  have hzero : AEStronglyMeasurable[F H] ((0 : Lp (State S) 2 μ) : Ω → State S) μ :=
    stronglyMeasurable_const.aestronglyMeasurable.congr (Lp.coeFn_zero (State S) 2 μ).symm
  have hsol0 := HeatTorusGalerkinBackward.exists_solution S P b H 0 hzero
  have ho {η : Lp (State S) 2 μ}
      (Y : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η) :
      ‖HeatBackwardDriver.state H η Y.drift 0‖ ^ 2 ≤ L *
        ‖HeatPredictableObservation.lift F μ H (observe S O) Y.predictableState‖ ^ 2 := by
    have he : ‖HeatPredictableObservation.lift F μ H (observe S O) Y.predictableState‖ ^ 2 = _ :=
      HeatTorusBackwardObservation.energy O Y
    rw [he]
    exact hobs S Y
  obtain ⟨u, hu, hc⟩ := HeatBackwardControlDuality.exists_cancelling_control (observe S O) hsol0 hL ho g
  refine ⟨u, hu, fun X hX0 hXH hD hN => ?_⟩
  obtain ⟨Y⟩ := HeatTorusGalerkinBackward.exists_solution S P b H (X.state H) hXH
  let f := HeatPredictableObservation.lift F μ H (inject S O) u
  have hf : MemLp (HeatBackwardEquationEnergy.slice f) 2 (timeMeasure H) :=
    HeatTimeLpField.square_integrable μ f (HeatPredictableObservation.measurable_process F μ H f) H
      (HeatPredictableObservation.ambient_memLp F μ H f)
  have hJ : StandardTerminalPastLocality (J H S) :=
    HeatTerminalNaturality.locality F μ H (HeatTorusGalerkinBackward.basis S)
      (HeatCanonicalNative.scalar H) (HeatCanonicalNative.locality H)
  have hterm := HeatTorusGalerkinTerminalDuality.terminal_pairing hJ hb Y X
    (HeatBackwardEquationEnergy.slice f) 0 hf (memLp_const (0 : Lp (State S) 2 μ)) hD
      (by simpa only [Pi.zero_apply, add_zero] using hN)
  have hcancel := hc Y
  change inner ℝ g (HeatBackwardDriver.state H (X.state H) Y.drift 0) +
    inner ℝ u (HeatTorusBackwardObservation.observation O Y) = 0 at hcancel
  rw [HeatTorusBackwardObservation.pairing O Y u] at hcancel
  simp only [Pi.zero_apply, inner_zero_left, integral_zero, add_zero, hX0] at hterm
  rw [hcancel, real_inner_self_eq_norm_sq] at hterm
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hterm)

end HeatTorusGalerkinControl

#print axioms HeatTorusGalerkinControl.exists_null_control
