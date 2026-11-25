import HeatBackwardSolutionLinear
import HeatHilbertControlDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatBackwardControlDuality

open MeasureTheory SHE SHE.PredictableL2 InnerProductSpace
open scoped NNReal ENNReal

variable {Ω E G : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  {J : StandardTerminalIto (C := E) (E := E) F μ H} {A M : E →L[ℝ] E}

private abbrev Pair (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (H : ℝ≥0) :=
  Lp E 2 μ × Process (E := G) F μ H

private def pair (B : E →L[ℝ] G) {η : Lp E 2 μ}
    (Y : HeatLocalBackwardEquation.Solution J A M 0 H η) : Pair (E := E) (G := G) F μ H :=
  (HeatBackwardDriver.state H η Y.drift 0, HeatPredictableObservation.lift F μ H B Y.predictableState)

omit [CompleteSpace G] in
private theorem pair_add (B : E →L[ℝ] G) {η ξ : Lp E 2 μ}
    (Y : HeatLocalBackwardEquation.Solution J A M 0 H η)
    (Z : HeatLocalBackwardEquation.Solution J A M 0 H ξ) :
    pair B (HeatBackwardSolutionLinear.add Y Z) = pair B Y + pair B Z := by
  apply Prod.ext
  · exact HeatBackwardSolutionLinear.state_add 0 H η ξ Y.drift Z.drift
  · exact (HeatPredictableObservation.lift F μ H B).map_add Y.predictableState Z.predictableState

omit [CompleteSpace G] in
private theorem pair_smul (B : E →L[ℝ] G) (c : ℝ) {η : Lp E 2 μ}
    (Y : HeatLocalBackwardEquation.Solution J A M 0 H η) :
    pair B (HeatBackwardSolutionLinear.smul c Y) = c • pair B Y := by
  apply Prod.ext
  · exact HeatBackwardSolutionLinear.state_smul 0 H c η Y.drift
  · exact (HeatPredictableObservation.lift F μ H B).map_smul c Y.predictableState

private def pairs (B : E →L[ℝ] G)
    (hz : Nonempty (HeatLocalBackwardEquation.Solution J A M 0 H 0)) :
    Submodule ℝ (Pair (E := E) (G := G) F μ H) where
  carrier := {p | ∃ (η : Lp E 2 μ) (Y : HeatLocalBackwardEquation.Solution J A M 0 H η),
    pair B Y = p}
  zero_mem' := by
    obtain ⟨Y⟩ := hz
    refine ⟨0 • (0 : Lp E 2 μ), HeatBackwardSolutionLinear.smul 0 Y, ?_⟩
    rw [pair_smul, zero_smul]
  add_mem' := by
    rintro _ _ ⟨η, Y, rfl⟩ ⟨ξ, Z, rfl⟩
    exact ⟨η + ξ, HeatBackwardSolutionLinear.add Y Z, pair_add B Y Z⟩
  smul_mem' := by
    rintro c _ ⟨η, Y, rfl⟩
    exact ⟨c • η, HeatBackwardSolutionLinear.smul c Y, pair_smul B c Y⟩

/-- A norm estimate for actual backward observations yields a predictable
control that cancels every backward pairing. The bound is the observed
control cost times the norm of the initial random state. -/
theorem exists_cancelling_control (B : E →L[ℝ] G)
    (hz : Nonempty (HeatLocalBackwardEquation.Solution J A M 0 H 0))
    {L : ℝ} (hL : 0 ≤ L)
    (hobs : ∀ {η : Lp E 2 μ} (Y : HeatLocalBackwardEquation.Solution J A M 0 H η),
      ‖HeatBackwardDriver.state H η Y.drift 0‖ ^ 2 ≤
        L * ‖HeatPredictableObservation.lift F μ H B Y.predictableState‖ ^ 2)
    (g : Lp E 2 μ) :
    ∃ u : Process (E := G) F μ H, ‖u‖ ≤ Real.sqrt L * ‖g‖ ∧
      ∀ {η : Lp E 2 μ} (Y : HeatLocalBackwardEquation.Solution J A M 0 H η),
        inner ℝ g (HeatBackwardDriver.state H η Y.drift 0) +
          inner ℝ u (HeatPredictableObservation.lift F μ H B Y.predictableState) = 0 := by
  let W := pairs B hz
  let obs : W →ₗ[ℝ] Process (E := G) F μ H := (LinearMap.snd ℝ _ _).comp W.subtype
  let init : W →ₗ[ℝ] Lp E 2 μ := (LinearMap.fst ℝ _ _).comp W.subtype
  let goal : W →ₗ[ℝ] ℝ := -(innerSL ℝ g).toLinearMap.comp init
  have hbound (w : W) : |goal w| ≤ (Real.sqrt L * ‖g‖) * ‖obs w‖ := by
    obtain ⟨η, Y, hw⟩ := w.property
    change |-(inner ℝ g w.val.1)| ≤ _ * ‖w.val.2‖
    rw [← hw, abs_neg]
    have hs : ‖(pair B Y).1‖ ≤ Real.sqrt L * ‖(pair B Y).2‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hL]
      exact hobs Y
    exact ((abs_real_inner_le_norm g _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))).trans_eq
      (by ring)
  obtain ⟨u, hu, hn⟩ := HeatHilbertControlDuality.exists_control_of_linear_bound obs goal
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hbound
  refine ⟨u, hn, ?_⟩
  intro η Y
  have hp : pair B Y ∈ W := ⟨η, Y, rfl⟩
  have h := hu ⟨pair B Y, hp⟩
  change inner ℝ u (HeatPredictableObservation.lift F μ H B Y.predictableState) =
    -inner ℝ g (HeatBackwardDriver.state H η Y.drift 0) at h
  rw [h, add_neg_cancel]

end HeatBackwardControlDuality

#print axioms HeatBackwardControlDuality.exists_cancelling_control
