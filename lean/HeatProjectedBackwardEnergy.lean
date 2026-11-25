import HeatBackwardEquationEnergy
import HeatL2Integrability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1850000
noncomputable section

namespace HeatProjectedBackwardEnergy

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.StoppedItoInputs
open HeatBackwardDriver (state)
open HeatBackwardEquationEnergy (slice)
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] [IsSeparable μ] {H : ℝ≥0}
  {J : StandardTerminalIto (C := E) (E := E) F μ H}
  {A B : E →L[ℝ] E} {η : Lp E 2 μ}

private theorem meas (u : Process (E := E) F μ H) : Measurable (u : ℝ≥0 × Ω → E) :=
  ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable

private theorem mem (u : Process (E := E) F μ H) : MemLp (u : ℝ≥0 × Ω → E) 2 (energyMeasure μ H) :=
  memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)

private theorem mem_slice (u : Process (E := E) F μ H) :
    MemLp (slice u) 2 (timeMeasure H) :=
  HeatTimeLpField.square_integrable μ u (meas u) H (mem u)

private theorem ae_slice (u : Process (E := E) F μ H) :
    ∀ᵐ t ∂timeMeasure H, (slice u t : Ω → E) =ᵐ[μ] fun ω => u (t, ω) :=
  HeatTimeLpField.value_ae μ u (meas u) H (mem u)

/-- The deterministic-time state has square-integrable time slices in the
space of square-integrable random variables. -/
theorem mem_state (S : HeatLocalBackwardEquation.Solution J A B 0 H η) :
    MemLp (state H η S.drift) 2 (timeMeasure H) := by
  have h : slice S.predictableState =ᵐ[timeMeasure H] state H η S.drift := by
    filter_upwards [S.state_slices, ae_slice S.predictableState, timeMeasure_ae_mem H]
      with t hs hp ht
    rw [indicator_of_mem ht] at hs
    exact Lp.ext (hp.trans hs)
  exact MemLp.ae_eq h (mem_slice S.predictableState)

def energy (Q : E →L[ℝ] E) (S : HeatLocalBackwardEquation.Solution J A B 0 H η) (t : ℝ≥0) : ℝ :=
  ‖(Q.compLpL 2 μ) (state H η S.drift t)‖ ^ 2

def density (Q : E →L[ℝ] E) (S : HeatLocalBackwardEquation.Solution J A B 0 H η) (t : ℝ≥0) : ℝ :=
  2 * inner ℝ (-(Q.compLpL 2 μ) (slice S.drift t)) ((Q.compLpL 2 μ) (state H η S.drift t)) +
    ‖(Q.compLpL 2 μ) (slice S.noise t)‖ ^ 2

theorem integrable_density (Q : E →L[ℝ] E) (S : HeatLocalBackwardEquation.Solution J A B 0 H η) :
    Integrable (density Q S) (timeMeasure H) := by
  let L := Q.compLpL 2 μ
  have h (g : ℝ≥0 → Lp E 2 μ) (hg : MemLp g 2 (timeMeasure H)) :
      MemLp (fun s => L (g s)) 2 (timeMeasure H) :=
    L.lipschitz.comp_memLp (map_zero L) hg
  exact ((HeatL2Integrability.inner (timeMeasure H) _ _
    ((h _ (mem_slice S.drift)).neg) (h _ (mem_state S))).const_mul 2).add
    ((h _ (mem_slice S.noise)).norm.integrable_sq)

/-- The expected squared norm of a deterministic projection obeys the
projected Itô identity, when the projection commutes with the original
terminal stochastic integral. The time integrand is in L¹. -/
theorem energy_prefix (hJ : StandardTerminalPastLocality J) (Q : E →L[ℝ] E)
    (hQ : ∀ u : Process (E := E) F μ H,
      (Q.compLpL 2 μ) (J.integral u) = J.integral (HeatPredictableLinearMap.map F μ H Q u))
    (S : HeatLocalBackwardEquation.Solution J A B 0 H η) {t : ℝ≥0} (ht : t ≤ H) :
    energy Q S t = energy Q S 0 + ∫ s, density Q S s ∂timeMeasure t := by
  let L := Q.compLpL 2 μ
  let Y (s : ℝ≥0) := L (state H η S.drift s)
  let f (s : ℝ≥0) := -L (slice S.drift s)
  let u := HeatPredictableLinearMap.map F μ H Q S.noise
  let Z (s : ℝ≥0) := L (slice S.noise s)
  have hf : Integrable f (timeMeasure H) := ((L.lipschitz.comp_memLp (map_zero L)
    (mem_slice S.drift)).integrable one_le_two).neg
  have hu : ∀ᵐ s ∂timeMeasure H, (fun ω => u (s, ω)) =ᵐ[μ] fun ω => Q (S.noise (s, ω)) :=
    Measure.ae_ae_of_ae_prod (HeatPredictableLinearMap.map_ae F μ H Q S.noise)
  have hZ : ∀ᵐ s ∂timeMeasure H, (fun ω => u (s, ω)) =ᵐ[μ] Z s := by
    filter_upwards [hu, ae_slice S.noise] with s hm hn
    filter_upwards [hm, hn, Q.coeFn_compLpL (slice S.noise s)] with ω hmω hnω hqω
    change u (s, ω) = L (slice S.noise s) ω
    rw [hqω, hnω, hmω]
  have lift_adapted (s : ℝ≥0) (x : Lp E 2 μ)
      (hx : AEStronglyMeasurable[F s] (x : Ω → E) μ) :
      AEStronglyMeasurable[F s] (L x : Ω → E) μ :=
    (Q.continuous.comp_aestronglyMeasurable hx).congr (Q.coeFn_compLpL x).symm
  have hY₀ : AEStronglyMeasurable[F 0] (Y 0 : Ω → E) μ :=
    lift_adapted 0 _ (HeatBackwardDriver.state_adapted H η S.drift 0)
  have hfa : ∀ᵐ s ∂timeMeasure H, AEStronglyMeasurable[F s] (f s : Ω → E) μ := by
    apply Eventually.of_forall
    intro s
    have hp : IsStronglyPredictable F (Function.curry (S.drift : ℝ≥0 × Ω → E)) :=
      Lp.stronglyMeasurable S.drift
    have hs := HeatTimeLpDrift.adapted μ S.drift F (fun r => hp.stronglyAdapted r) s
    exact (lift_adapted s _ hs).neg.congr (Lp.coeFn_neg _).symm
  have hY (s : ℝ≥0) (hs : s ≤ H) : Y s = Y 0 +
      HeatDeterministicPairing.cumulative (timeMeasure H) f s + HeatStoppedPairing.value F μ H J u s := by
    have he := congrArg L (HeatBackwardEquationEnergy.forward_form S hs)
    rw [map_add, map_sub] at he
    have hd : HeatDeterministicPairing.cumulative (timeMeasure H) f s =
        -L (HeatPredictableDriftCell.value 0 s S.drift) := by
      rw [← HeatBackwardEquationEnergy.cumulative_eq S.drift hs]
      unfold HeatDeterministicPairing.cumulative
      dsimp only [f]
      rw [integral_neg, L.integral_comp_comm ((mem_slice S.drift).integrable one_le_two).integrableOn]
    have hstop : L (J.integral (stop F μ H s S.noise)) = HeatStoppedPairing.value F μ H J u s := by
      change (Q.compLpL 2 μ) (J.integral (stop F μ H s S.noise)) = _
      rw [hQ, HeatPredictableLinearMap.stop_commutes]
      rfl
    simpa only [hd, sub_eq_add_neg, hstop] using he
  have h := HeatTerminalItoCompression.energy_prefix J hJ ht (Y 0) hY₀ f hf hfa u Y Z hZ hY
  have hmono := HeatTimeRestriction.mono ht
  have hi : Integrable (fun s => inner ℝ (f s) (Y s)) (timeMeasure t) :=
    (HeatL2Integrability.inner (timeMeasure H) _ _
      (L.lipschitz.comp_memLp (map_zero L) (mem_slice S.drift)).neg
      (L.lipschitz.comp_memLp (map_zero L) (mem_state S))).mono_measure hmono
  have hz : Integrable (fun s => ‖Z s‖ ^ 2) (timeMeasure t) :=
    (L.lipschitz.comp_memLp (map_zero L) (mem_slice S.noise)).norm.integrable_sq.mono_measure hmono
  change ‖Y t‖ ^ 2 = ‖Y 0‖ ^ 2 + ∫ s, (2 * inner ℝ (f s) (Y s) + ‖Z s‖ ^ 2) ∂timeMeasure t
  rw [integral_add (hi.const_mul 2) hz, integral_const_mul]
  linarith

end HeatProjectedBackwardEnergy

#print axioms HeatProjectedBackwardEnergy.energy_prefix
#print axioms HeatProjectedBackwardEnergy.integrable_density
