import HeatBackwardDriverProcess
import HeatPredictableLinearMap
import SHE.StoppedInputAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace HeatLocalBackwardEquation

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open HeatBackwardDriver (state terminal mean)
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

private abbrev applyToProcess (A : E →L[ℝ] E) (v : Process (E := E) F μ H) :
    Process (E := E) F μ H := HeatPredictableLinearMap.map F μ H A v

private theorem map_sub (A : E →L[ℝ] E) (u v : Process (E := E) F μ H) :
    applyToProcess A u - applyToProcess A v = applyToProcess A (u - v) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (_root_.map_sub (A.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u v).symm

private theorem norm_map_le (A : E →L[ℝ] E) (u : Process (E := E) F μ H) :
    ‖applyToProcess A u‖ ≤ ‖A‖ * ‖u‖ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let L := A.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))
  exact (L.le_opNorm u).trans (mul_le_mul_of_nonneg_right (A.norm_compLpL_le ..) (norm_nonneg _))

private theorem post_post {a t : ℝ≥0} (hat : a ≤ t) (u : Process (E := E) F μ H) :
    post F μ H t (post F μ H a u) = post F μ H t u := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [post_ae F μ H t (post F μ H a u), post_ae F μ H a u, post_ae F μ H t u]
    with p hta ha ht
  rw [hta, ht, ha]
  by_cases hp : t < p.1
  · simp only [hp, hat.trans_lt hp, if_pos]
  · simp only [hp, if_false]

/-- A solution of the bounded linear backward equation on one time cell.
Its state is represented jointly in predictable L² and its noise is supported
on the cell, with both processes on the original time horizon. -/
structure Solution (J : StandardTerminalIto (C := E) (E := E) F μ H)
    (A B : E →L[ℝ] E) (a b : ℝ≥0) (η : Lp E 2 μ) where
  drift : Process (E := E) F μ H
  noise : Process (E := E) F μ H
  predictableState : Process (E := E) F μ H
  state_slices : HeatBackwardDriverProcess.Realizes a b η drift predictableState
  drift_eq : drift =
    HeatPredictableLinearMap.map F μ H A predictableState + HeatPredictableLinearMap.map F μ H B noise
  noise_before : stop F μ H a noise = 0
  noise_after : stop F μ H b noise = noise
  endpoint : state b η drift b = η
  equation : ∀ t, a ≤ t → t ≤ b → state b η drift t =
    η + HeatPredictableDriftCell.value t b drift - J.integral (post F μ H t noise)

/-- Existence on a short cell by a contraction of the prescribed drift.
The length condition is expressed in terms of the actual operator norms. -/
theorem exists_solution (J : StandardTerminalIto (C := E) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hrep : ∀ X : Lp E 2 μ, AEStronglyMeasurable[F H] (X : Ω → E) μ →
      (∫ ω, X ω ∂μ) = 0 → ∃ u : Process (E := E) F μ H, J.integral u = X)
    (A B : E →L[ℝ] E) {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H)
    (hshort : 2 * (‖A‖ ^ 2 * ((b : ℝ) - a) ^ 2 + ‖B‖ ^ 2 * ((b : ℝ) - a)) ≤ 1 / 4)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[F b] (η : Ω → E) μ) :
    Nonempty (Solution J A B a b η) := by
  classical
  choose u hu hstop using fun f : Process (E := E) F μ H =>
    HeatBackwardDriver.exists_noise J hJ hrep hb η hη f
  choose v hv using fun f => HeatBackwardDriverProcess.exists_state_process J hJ hnull hb η f (u f) (hu f)
  let Z (f : Process (E := E) F μ H) := post F μ H a (u f)
  let Φ (f : Process (E := E) F μ H) := applyToProcess A (v f) + applyToProcess B (Z f)
  let δ : ℝ := b - a
  have hLip : LipschitzWith (1 / 2) Φ := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    rw [dist_eq_norm, dist_eq_norm]
    change ‖Φ f - Φ g‖ ≤ (1 / 2 : ℝ) * ‖f - g‖
    have hstate := HeatBackwardDriverProcess.norm_sq_sub_le hab hb η f g _ _ (hv f) (hv g)
    have hnoise := HeatBackwardDriver.noise_norm_sq_sub_le J hJ hab hb η f g _ _ (hu f) (hu g)
    have ha : ‖applyToProcess A (v f - v g)‖ ^ 2 ≤ ‖A‖ ^ 2 * (δ ^ 2 * ‖f - g‖ ^ 2) := by
      calc
        _ ≤ (‖A‖ * ‖v f - v g‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_map_le A _) 2
        _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hstate (sq_nonneg _)
    have hb' : ‖applyToProcess B (Z f - Z g)‖ ^ 2 ≤ ‖B‖ ^ 2 * (δ * ‖f - g‖ ^ 2) := by
      calc
        _ ≤ (‖B‖ * ‖Z f - Z g‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_map_le B _) 2
        _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hnoise (sq_nonneg _)
    have hsum : Φ f - Φ g = applyToProcess A (v f - v g) + applyToProcess B (Z f - Z g) := by
      dsimp only [Φ]
      rw [← map_sub, ← map_sub]
      abel
    have hsq : ‖Φ f - Φ g‖ ^ 2 ≤ ((1 / 2 : ℝ) * ‖f - g‖) ^ 2 := by
      rw [hsum]
      calc
        _ ≤ (‖applyToProcess A (v f - v g)‖ + ‖applyToProcess B (Z f - Z g)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        _ ≤ 2 * (‖applyToProcess A (v f - v g)‖ ^ 2 + ‖applyToProcess B (Z f - Z g)‖ ^ 2) := by
          nlinarith [sq_nonneg (‖applyToProcess A (v f - v g)‖ - ‖applyToProcess B (Z f - Z g)‖)]
        _ ≤ 2 * (‖A‖ ^ 2 * (δ ^ 2 * ‖f - g‖ ^ 2) + ‖B‖ ^ 2 * (δ * ‖f - g‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add ha hb') (by norm_num)
        _ = (2 * (‖A‖ ^ 2 * δ ^ 2 + ‖B‖ ^ 2 * δ)) * ‖f - g‖ ^ 2 := by ring
        _ ≤ _ := by
          calc
            _ ≤ (1 / 4) * ‖f - g‖ ^ 2 := mul_le_mul_of_nonneg_right hshort (sq_nonneg _)
            _ = _ := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  have hcon : ContractingWith (1 / 2) Φ := ⟨by norm_num, hLip⟩
  let f := hcon.fixedPoint Φ
  have hf : f = Φ f := hcon.fixedPoint_isFixedPt.symm
  have hZ : Z f = stop F μ H b (u f) - stop F μ H a (u f) := by
    change post F μ H a (u f) = _
    simpa only [hstop f] using PastItoAlgebra.post_stop_eq_sub F μ H a b hab (u f)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  refine ⟨⟨f, Z f, v f, hv f, hf, ?_, ?_, HeatBackwardDriver.state_terminal b η hη f, ?_⟩⟩
  · rw [hZ, StoppedDampingClock.stop_sub, StoppedInputAlgebra.stop_stop, StoppedInputAlgebra.stop_stop,
      min_eq_left hab', min_self, sub_self]
  · rw [hZ, StoppedDampingClock.stop_sub, StoppedInputAlgebra.stop_stop, StoppedInputAlgebra.stop_stop,
      min_self, min_eq_right hab']
  · intro t hat htb
    change _ = _ - J.integral (post F μ H t (post F μ H a (u f)))
    rw [post_post hat]
    exact HeatBackwardDriver.equation J hJ hat htb hb η f (u f) (hu f)

end HeatLocalBackwardEquation

#print axioms HeatLocalBackwardEquation.exists_solution
