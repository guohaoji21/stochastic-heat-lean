import HeatTerminalItoCompression
import HeatL2Integrability
import SHE.TwoChannelItoRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace HeatItoProductEnergy

open Filter MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- An additive Itô trajectory represented by the common terminal integral.
Its time slices, drift and diffusion are all square-integrable. -/
structure Trajectory (J : StandardTerminalIto (C := E) (E := E) F μ H) where
  state : ℝ≥0 → Lp E 2 μ
  drift : ℝ≥0 → Lp E 2 μ
  noise : ℝ≥0 → Lp E 2 μ
  process : Process (E := E) F μ H
  state_square : MemLp state 2 (timeMeasure H)
  drift_square : MemLp drift 2 (timeMeasure H)
  noise_square : MemLp noise 2 (timeMeasure H)
  initial_adapted : AEStronglyMeasurable[F 0] (state 0 : Ω → E) μ
  drift_adapted : ∀ᵐ s ∂timeMeasure H, AEStronglyMeasurable[F s] (drift s : Ω → E) μ
  noise_slices : ∀ᵐ s ∂timeMeasure H, (fun ω => process (s, ω)) =ᵐ[μ] noise s
  equation : ∀ s, s ≤ H → state s = state 0 +
    HeatDeterministicPairing.cumulative (timeMeasure H) drift s + HeatStoppedPairing.value F μ H J process s

variable {J : StandardTerminalIto (C := E) (E := E) F μ H}

private def add (X Y : Trajectory J) : Trajectory J where
  state s := X.state s + Y.state s
  drift s := X.drift s + Y.drift s
  noise s := X.noise s + Y.noise s
  process := X.process + Y.process
  state_square := X.state_square.add Y.state_square
  drift_square := X.drift_square.add Y.drift_square
  noise_square := X.noise_square.add Y.noise_square
  initial_adapted := (X.initial_adapted.add Y.initial_adapted).congr (Lp.coeFn_add _ _).symm
  drift_adapted := by
    filter_upwards [X.drift_adapted, Y.drift_adapted] with s hx hy
    exact (hx.add hy).congr (Lp.coeFn_add _ _).symm
  noise_slices := by
    have hs := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_add X.process Y.process))
    filter_upwards [hs, X.noise_slices, Y.noise_slices] with s hs hx hy
    filter_upwards [hs, hx, hy, Lp.coeFn_add (X.noise s) (Y.noise s)] with ω hs hx hy hxy
    rw [hs, hxy, Pi.add_apply, Pi.add_apply, hx, hy]
  equation s hs := by
    rw [X.equation s hs, Y.equation s hs]
    unfold HeatDeterministicPairing.cumulative HeatStoppedPairing.value
    rw [integral_add (X.drift_square.integrable one_le_two).integrableOn
      (Y.drift_square.integrable one_le_two).integrableOn,
      TwoChannelItoRows.stop_add, map_add]
    abel

private theorem energy (hJ : StandardTerminalPastLocality J) (X : Trajectory J) :
    ‖X.state H‖ ^ 2 - ‖X.state 0‖ ^ 2 =
      2 * (∫ s, inner ℝ (X.drift s) (X.state s) ∂timeMeasure H) +
        ∫ s, ‖X.noise s‖ ^ 2 ∂timeMeasure H :=
  HeatTerminalItoCompression.energy_prefix J hJ le_rfl (X.state 0) X.initial_adapted X.drift
    (X.drift_square.integrable one_le_two) X.drift_adapted X.process X.state X.noise X.noise_slices X.equation

/-- The expected Itô product rule for two trajectories represented by the
same stochastic integral, including the pairing of their diffusions. -/
theorem product (hJ : StandardTerminalPastLocality J) (X Y : Trajectory J) :
    inner ℝ (X.state H) (Y.state H) - inner ℝ (X.state 0) (Y.state 0) =
      (∫ s, inner ℝ (X.drift s) (Y.state s) ∂timeMeasure H) +
      (∫ s, inner ℝ (Y.drift s) (X.state s) ∂timeMeasure H) +
      ∫ s, inner ℝ (X.noise s) (Y.noise s) ∂timeMeasure H := by
  let ν := timeMeasure H
  have h11 := HeatL2Integrability.inner ν _ _ X.drift_square X.state_square
  have h12 := HeatL2Integrability.inner ν _ _ X.drift_square Y.state_square
  have h21 := HeatL2Integrability.inner ν _ _ Y.drift_square X.state_square
  have h22 := HeatL2Integrability.inner ν _ _ Y.drift_square Y.state_square
  have hZ := HeatL2Integrability.inner ν _ _ X.noise_square Y.noise_square
  have hD : (∫ s, inner ℝ ((add X Y).drift s) ((add X Y).state s) ∂ν) =
      ((∫ s, inner ℝ (X.drift s) (X.state s) ∂ν) + ∫ s, inner ℝ (Y.drift s) (X.state s) ∂ν) +
      ((∫ s, inner ℝ (X.drift s) (Y.state s) ∂ν) + ∫ s, inner ℝ (Y.drift s) (Y.state s) ∂ν) := by
    simp only [add, inner_add_left, inner_add_right]
    have ha : Integrable (fun s => inner ℝ (X.drift s) (X.state s) + inner ℝ (Y.drift s) (X.state s)) ν := h11.add h21
    have hb : Integrable (fun s => inner ℝ (X.drift s) (Y.state s) + inner ℝ (Y.drift s) (Y.state s)) ν := h12.add h22
    rw [integral_add ha hb, integral_add h11 h21, integral_add h12 h22]
  have hN : (∫ s, ‖(add X Y).noise s‖ ^ 2 ∂ν) =
      ((∫ s, ‖X.noise s‖ ^ 2 ∂ν) + 2 * ∫ s, inner ℝ (X.noise s) (Y.noise s) ∂ν) +
      ∫ s, ‖Y.noise s‖ ^ 2 ∂ν := by
    simp only [add, norm_add_sq_real]
    have hXn : Integrable (fun s => ‖X.noise s‖ ^ 2) ν := X.noise_square.norm.integrable_sq
    have hYn : Integrable (fun s => ‖Y.noise s‖ ^ 2) ν := Y.noise_square.norm.integrable_sq
    have hXY : Integrable (fun s => 2 * inner ℝ (X.noise s) (Y.noise s)) ν := hZ.const_mul 2
    have ha : Integrable (fun s => ‖X.noise s‖ ^ 2 + 2 * inner ℝ (X.noise s) (Y.noise s)) ν := hXn.add hXY
    rw [integral_add ha hYn, integral_add hXn hXY,
      integral_const_mul (2 : ℝ) (fun s => inner ℝ (X.noise s) (Y.noise s))]
  have h := energy hJ (add X Y)
  change ‖X.state H + Y.state H‖ ^ 2 - ‖X.state 0 + Y.state 0‖ ^ 2 = _ at h
  rw [hD, hN, norm_add_sq_real, norm_add_sq_real] at h
  linarith [energy hJ X, energy hJ Y]

/-- Terminal duality for an additive forward and backward pair. An error in
the forward diffusion gives exactly one additional diffusion pairing. -/
theorem terminal_duality (hJ : StandardTerminalPastLocality J) (X Y : Trajectory J)
    (A M : Lp E 2 μ →L[ℝ] Lp E 2 μ) (f err : ℝ≥0 → Lp E 2 μ)
    (hf : MemLp f 2 (timeMeasure H)) (he : MemLp err 2 (timeMeasure H))
    (hX : ∀ᵐ s ∂timeMeasure H, X.drift s = A (X.state s) + f s)
    (hY : ∀ᵐ s ∂timeMeasure H, Y.drift s = -(A.adjoint (Y.state s)) - M.adjoint (Y.noise s))
    (hN : ∀ᵐ s ∂timeMeasure H, X.noise s = M (X.state s) + err s) :
    inner ℝ (X.state H) (Y.state H) = inner ℝ (X.state 0) (Y.state 0) +
      (∫ s, inner ℝ (f s) (Y.state s) ∂timeMeasure H) +
      ∫ s, inner ℝ (err s) (Y.noise s) ∂timeMeasure H := by
  let ν := timeMeasure H
  have hprod := product hJ X Y
  have hXd := HeatL2Integrability.inner ν _ _ X.drift_square Y.state_square
  have hYd := HeatL2Integrability.inner ν _ _ Y.drift_square X.state_square
  have hi : Integrable (fun s => inner ℝ (X.drift s) (Y.state s) + inner ℝ (Y.drift s) (X.state s)) ν := hXd.add hYd
  rw [← integral_add hXd hYd, ← integral_add hi
    (HeatL2Integrability.inner ν _ _ X.noise_square Y.noise_square)] at hprod
  have hcancel : (fun s => inner ℝ (X.drift s) (Y.state s) + inner ℝ (Y.drift s) (X.state s) +
      inner ℝ (X.noise s) (Y.noise s)) =ᵐ[ν]
      fun s => inner ℝ (f s) (Y.state s) + inner ℝ (err s) (Y.noise s) := by
    filter_upwards [hX, hY, hN] with s hx hy hn
    rw [hx, hy, hn, inner_add_left, inner_add_left, inner_sub_left, inner_neg_left]
    have hA : inner ℝ (A.adjoint (Y.state s)) (X.state s) = inner ℝ (A (X.state s)) (Y.state s) :=
      (real_inner_comm _ _).trans (A.adjoint_inner_right _ _)
    have hM : inner ℝ (M.adjoint (Y.noise s)) (X.state s) = inner ℝ (M (X.state s)) (Y.noise s) :=
      (real_inner_comm _ _).trans (M.adjoint_inner_right _ _)
    rw [hA, hM]
    ring
  rw [integral_congr_ae hcancel, integral_add (HeatL2Integrability.inner ν _ _ hf Y.state_square)
    (HeatL2Integrability.inner ν _ _ he Y.noise_square)] at hprod
  linarith

end HeatItoProductEnergy

#print axioms HeatItoProductEnergy.product
#print axioms HeatItoProductEnergy.terminal_duality
