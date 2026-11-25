import HeatItoProductEnergy
import HeatProjectedBackwardEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1650000
noncomputable section

namespace HeatBackwardProductTrajectory

open Filter MeasureTheory Set SHE SHE.PredictableL2
open HeatBackwardDriver (state)
open HeatBackwardEquationEnergy (slice)
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] [IsSeparable μ] {H : ℝ≥0}
  {J : StandardTerminalIto (C := E) (E := E) F μ H}
  {A B : E →L[ℝ] E} {η : Lp E 2 μ}

private theorem slice_properties (u : Process (E := E) F μ H) :
    MemLp (slice u) 2 (timeMeasure H) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] slice u t) := by
  have hm : Measurable (u : ℝ≥0 × Ω → E) :=
    ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
  have hi : MemLp (u : ℝ≥0 × Ω → E) 2 (energyMeasure μ H) :=
    memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  exact ⟨HeatTimeLpField.square_integrable μ u hm H hi,
    (HeatTimeLpField.value_ae μ u hm H hi).mono fun _ h => h.symm⟩

/-- The actual backward solution, with the drift sign appropriate to the
forward-time additive Itô representation. -/
def trajectory (U : HeatLocalBackwardEquation.Solution J A B 0 H η) : HeatItoProductEnergy.Trajectory J where
  state := state H η U.drift
  drift s := -slice U.drift s
  noise := slice U.noise
  process := U.noise
  state_square := HeatProjectedBackwardEnergy.mem_state U
  drift_square := (slice_properties U.drift).1.neg
  noise_square := (slice_properties U.noise).1
  initial_adapted := HeatBackwardDriver.state_adapted H η U.drift 0
  drift_adapted := by
    apply Eventually.of_forall
    intro s
    have hp : IsStronglyPredictable F (Function.curry (U.drift : ℝ≥0 × Ω → E)) := Lp.stronglyMeasurable U.drift
    exact (HeatTimeLpDrift.adapted μ U.drift F (fun r => hp.stronglyAdapted r) s).neg.congr
      (Lp.coeFn_neg _).symm
  noise_slices := (slice_properties U.noise).2
  equation s hs := by
    have hd : HeatDeterministicPairing.cumulative (timeMeasure H) (fun t => -slice U.drift t) s =
        -HeatPredictableDriftCell.value 0 s U.drift := by
      rw [← HeatBackwardEquationEnergy.cumulative_eq U.drift hs]
      exact integral_neg _
    rw [hd]
    simpa only [sub_eq_add_neg, HeatStoppedPairing.value] using HeatBackwardEquationEnergy.forward_form U hs

private theorem dissipative_lp (hA : ∀ x, inner ℝ (A x) x ≤ 0) (x : Lp E 2 μ) :
    inner ℝ ((A.compLpL 2 μ) x) x ≤ 0 := by
  rw [L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [A.coeFn_compLpL x] with ω hω
  rw [hω]
  exact hA _

/-- Dissipativity and a uniform state bound control the full time integral
of the noise energy. The bound only uses the operator norm of the noise
coupling and the uniform constant for the state. -/
theorem noise_energy_le (hJ : StandardTerminalPastLocality J)
    (U : HeatLocalBackwardEquation.Solution J A B 0 H η)
    (hA : ∀ x, inner ℝ (A x) x ≤ 0) {M : ℝ}
    (hstate : ∀ t ≤ H, ‖state H η U.drift t‖ ^ 2 ≤ M * ‖η‖ ^ 2) :
    (∫ t, ‖slice U.noise t‖ ^ 2 ∂timeMeasure H) ≤
      (2 + 4 * ‖B‖ ^ 2 * (H : ℝ) * M) * ‖η‖ ^ 2 := by
  let X := state H η U.drift
  let D := slice U.drift
  let Z := slice U.noise
  let ν := timeMeasure H
  let β := ‖B‖
  have hBL (z : Lp E 2 μ) : ‖(B.compLpL 2 μ) z‖ ≤ β * ‖z‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [B.coeFn_compLpL z] with ω hω
    rw [hω]
    exact B.le_opNorm _
  have hpoint : ∀ᵐ t ∂ν, (1 / 2 : ℝ) * ‖Z t‖ ^ 2 - (2 * β ^ 2) * ‖X t‖ ^ 2 ≤
      2 * inner ℝ (-D t) (X t) + ‖Z t‖ ^ 2 := by
    filter_upwards [HeatBackwardEquationEnergy.drift_slices U] with t ht
    change D t = (A.compLpL 2 μ) (X t) + (B.compLpL 2 μ) (Z t) at ht
    have hc : inner ℝ ((B.compLpL 2 μ) (Z t)) (X t) ≤ β * ‖Z t‖ * ‖X t‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hBL _) (norm_nonneg _))
    rw [ht, inner_neg_left, inner_add_left]
    nlinarith [dissipative_lp hA (X t), sq_nonneg (‖Z t‖ - 2 * β * ‖X t‖)]
  have hXi : Integrable (fun t => ‖X t‖ ^ 2) ν := (HeatProjectedBackwardEnergy.mem_state U).norm.integrable_sq
  have hZi : Integrable (fun t => ‖Z t‖ ^ 2) ν := (slice_properties U.noise).1.norm.integrable_sq
  have hDi : Integrable (fun t => inner ℝ (-D t) (X t)) ν :=
    HeatL2Integrability.inner ν _ _ (slice_properties U.drift).1.neg (HeatProjectedBackwardEnergy.mem_state U)
  have hi := integral_mono_ae ((hZi.const_mul (1 / 2)).sub (hXi.const_mul (2 * β ^ 2)))
    ((hDi.const_mul 2).add hZi) hpoint
  change (∫ t, ((1 / 2 : ℝ) * ‖Z t‖ ^ 2 - (2 * β ^ 2) * ‖X t‖ ^ 2) ∂ν) ≤
    ∫ t, (2 * inner ℝ (-D t) (X t) + ‖Z t‖ ^ 2) ∂ν at hi
  rw [integral_sub (hZi.const_mul _) (hXi.const_mul _), integral_add (hDi.const_mul _) hZi,
    integral_const_mul _ (fun t => ‖Z t‖ ^ 2), integral_const_mul _ (fun t => ‖X t‖ ^ 2),
    integral_const_mul _ (fun t => inner ℝ (-D t) (X t))] at hi
  have henergy := HeatBackwardEquationEnergy.energy_prefix hJ U le_rfl
  change ‖X H‖ ^ 2 - ‖X 0‖ ^ 2 = 2 * (∫ t, inner ℝ (-D t) (X t) ∂ν) + ∫ t, ‖Z t‖ ^ 2 ∂ν at henergy
  have hη : X H = η := U.endpoint
  rw [hη] at henergy
  have hmass : ν.real univ = (H : ℝ) := by rw [Measure.real, timeMeasure_mass]; simp
  have hb := integral_mono_ae hXi (integrable_const (M * ‖η‖ ^ 2))
    ((timeMeasure_ae_mem H).mono fun t ht => hstate t ht.2)
  change (∫ t, ‖X t‖ ^ 2 ∂ν) ≤ ∫ _ : ℝ≥0, M * ‖η‖ ^ 2 ∂ν at hb
  rw [integral_const, hmass, smul_eq_mul] at hb
  have hbb := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * β ^ 2 by positivity)
  change (∫ t, ‖Z t‖ ^ 2 ∂ν) ≤ (2 + 4 * β ^ 2 * (H : ℝ) * M) * ‖η‖ ^ 2
  nlinarith [sq_nonneg ‖X 0‖]

end HeatBackwardProductTrajectory

#print axioms HeatBackwardProductTrajectory.trajectory
#print axioms HeatBackwardProductTrajectory.noise_energy_le
