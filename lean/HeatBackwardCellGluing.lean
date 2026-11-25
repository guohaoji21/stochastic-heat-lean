import HeatLocalBackwardEquation
import HeatBackwardCellSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatBackwardCellGluing

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.PastItoInputs
open HeatBackwardDriver (state)
open HeatBackwardCellSupport (Supported)
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

private theorem disjoint_cells {a b c d : ℝ≥0} (hbc : b ≤ c) :
    Disjoint (Ioc a b) (Ioc c d) :=
  Set.disjoint_left.mpr fun _ h₁ h₂ => not_lt_of_ge (h₁.2.trans hbc) h₂.1

private theorem map_add (A : E →L[ℝ] E) (u v : Process (E := E) F μ H) :
    HeatPredictableLinearMap.map F μ H A (u + v) =
      HeatPredictableLinearMap.map F μ H A u + HeatPredictableLinearMap.map F μ H A v := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact _root_.map_add (A.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u v

private theorem drift_supported
    {J : StandardTerminalIto (C := E) (E := E) F μ H}
    {A B : E →L[ℝ] E} {a b : ℝ≥0} {η : Lp E 2 μ}
    (S : HeatLocalBackwardEquation.Solution J A B a b η) : Supported a b S.drift := by
  rw [S.drift_eq]
  exact HeatBackwardCellSupport.same_add
    (HeatBackwardCellSupport.map (HeatBackwardCellSupport.of_state S.state_slices) A)
    (HeatBackwardCellSupport.map (HeatBackwardCellSupport.of_stops S.noise_before S.noise_after) B)

private theorem state_eq_of_adapted (J : StandardTerminalIto (C := E) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (t b : ℝ≥0)
    (η z : Lp E 2 μ) (f u : Process (E := E) F μ H)
    (hz : AEStronglyMeasurable[F t] (z : Ω → E) μ)
    (he : z = η + HeatPredictableDriftCell.value t b f - J.integral (post F μ H t u)) :
    state b η f t = z := by
  letI : Fact (F t ≤ mΩ) := ⟨F.le t⟩
  let K := lpMeas E ℝ (F t) 2 μ
  change K.starProjection (η + HeatPredictableDriftCell.value t b f) = z
  apply K.eq_starProjection_of_mem_orthogonal (mem_lpMeas_iff_aestronglyMeasurable.mpr hz)
  rw [show η + HeatPredictableDriftCell.value t b f - z = J.integral (post F μ H t u) by rw [he]; abel]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  rw [real_inner_comm]
  exact HeatPastPairing.future_orthogonal J hJ t u y (mem_lpMeas_iff_aestronglyMeasurable.mp hy)

/-- Join adjacent cells using the left endpoint value of the later solution
as the earlier terminal value. The predictable inputs and Itô integral stay
on the original horizon. -/
def glue (J : StandardTerminalIto (C := E) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) {A B : E →L[ℝ] E}
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b) (η : Lp E 2 μ)
    (R : HeatLocalBackwardEquation.Solution J A B c b η)
    (L : HeatLocalBackwardEquation.Solution J A B a c (state b η R.drift c)) :
    HeatLocalBackwardEquation.Solution J A B a b η := by
  classical
  let f := L.drift + R.drift
  let u := L.noise + R.noise
  let w := L.predictableState + R.predictableState
  let X (t : ℝ≥0) := if t ≤ c then state c (state b η R.drift c) L.drift t else state b η R.drift t
  have hLf := drift_supported L
  have hRf := drift_supported R
  have hLu := HeatBackwardCellSupport.of_stops L.noise_before L.noise_after
  have hRu := HeatBackwardCellSupport.of_stops R.noise_before R.noise_after
  have hX (t : ℝ≥0) : AEStronglyMeasurable[F t] (X t : Ω → E) μ := by
    by_cases ht : t ≤ c
    · simpa only [X, if_pos ht] using HeatBackwardDriver.state_adapted c (state b η R.drift c) L.drift t
    · simpa only [X, if_neg ht] using HeatBackwardDriver.state_adapted b η R.drift t
  have heq (t : ℝ≥0) (ht : a ≤ t) (ht' : t ≤ b) :
      X t = η + HeatPredictableDriftCell.value t b f - J.integral (post F μ H t u) := by
    by_cases htc : t ≤ c
    · have hR := R.equation c le_rfl hcb
      rw [HeatBackwardCellSupport.post_eq_of_le le_rfl hRu] at hR
      have hd : HeatPredictableDriftCell.value t b f =
          HeatPredictableDriftCell.value t c L.drift + HeatPredictableDriftCell.value c b R.drift := by
        dsimp only [f]
        rw [HeatBackwardCellSupport.drift_add, HeatPredictableDriftCell.split htc hcb L.drift,
          HeatPredictableDriftCell.split htc hcb R.drift,
          HeatBackwardCellSupport.drift_zero hLf (disjoint_cells le_rfl),
          HeatBackwardCellSupport.drift_zero hRf (disjoint_cells le_rfl).symm, add_zero, zero_add]
      simp only [X, if_pos htc]
      rw [L.equation t ht htc, hd]
      dsimp only [u]
      rw [PastItoAlgebra.post_add, HeatBackwardCellSupport.post_eq_of_le htc hRu, _root_.map_add]
      calc
        _ = (η + HeatPredictableDriftCell.value c b R.drift - J.integral R.noise) +
            HeatPredictableDriftCell.value t c L.drift - J.integral (post F μ H t L.noise) :=
          congrArg (fun z => z + HeatPredictableDriftCell.value t c L.drift -
            J.integral (post F μ H t L.noise)) hR
        _ = _ := by abel
    · have hct := (lt_of_not_ge htc).le
      simp only [X, if_neg htc]
      rw [R.equation t hct ht']
      dsimp only [f, u]
      rw [HeatBackwardCellSupport.drift_add,
        HeatBackwardCellSupport.drift_zero hLf (disjoint_cells hct), zero_add,
        PastItoAlgebra.post_add, HeatBackwardCellSupport.post_zero_of_ge hct hLu, zero_add]
  have hstate (t : ℝ≥0) (ht : a ≤ t) (ht' : t ≤ b) : state b η f t = X t :=
    state_eq_of_adapted J hJ t b η (X t) f u (hX t) (heq t ht ht')
  have hw : HeatBackwardDriverProcess.Realizes a b η f w := by
    unfold HeatBackwardDriverProcess.Realizes
    filter_upwards [L.state_slices, R.state_slices,
      Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_add L.predictableState R.predictableState))]
      with t hl hr hsum
    by_cases htl : t ∈ Ioc a c
    · have htr : t ∉ Ioc c b := fun h => not_lt_of_ge htl.2 h.1
      have htb : t ∈ Ioc a b := ⟨htl.1, htl.2.trans hcb⟩
      rw [indicator_of_mem htl] at hl
      rw [indicator_of_notMem htr] at hr
      rw [indicator_of_mem htb, hstate t htb.1.le htb.2]
      filter_upwards [hl, hr, hsum] with ω hl hr hsum
      simp only [w, hsum, Pi.add_apply, hl, hr, Pi.zero_apply, add_zero, X, if_pos htl.2]
    · by_cases htr : t ∈ Ioc c b
      · have htb : t ∈ Ioc a b := ⟨hac.trans_lt htr.1, htr.2⟩
        rw [indicator_of_notMem htl] at hl
        rw [indicator_of_mem htr] at hr
        rw [indicator_of_mem htb, hstate t htb.1.le htb.2]
        filter_upwards [hl, hr, hsum] with ω hl hr hsum
        simp only [w, hsum, Pi.add_apply, hl, hr, Pi.zero_apply, zero_add, X, if_neg (not_le_of_gt htr.1)]
      · have htb : t ∉ Ioc a b := by
          rw [← Ioc_union_Ioc_eq_Ioc hac hcb]
          exact fun h => h.elim htl htr
        rw [indicator_of_notMem htl] at hl
        rw [indicator_of_notMem htr] at hr
        rw [indicator_of_notMem htb]
        filter_upwards [hl, hr, hsum] with ω hl hr hsum
        simp only [w, hsum, Pi.add_apply, hl, hr, Pi.zero_apply, zero_add]
  have hs := HeatBackwardCellSupport.stops (HeatBackwardCellSupport.add hac hcb hLu hRu)
  refine ⟨f, u, w, hw, ?_, hs.1, hs.2, ?_, fun t ht ht' => (hstate t ht ht').trans (heq t ht ht')⟩
  · dsimp only [f, u, w]
    calc
      _ = (HeatPredictableLinearMap.map F μ H A L.predictableState +
            HeatPredictableLinearMap.map F μ H B L.noise) +
          (HeatPredictableLinearMap.map F μ H A R.predictableState +
            HeatPredictableLinearMap.map F μ H B R.noise) :=
        congrArg₂ (· + ·) L.drift_eq R.drift_eq
      _ = _ := by rw [map_add, map_add]; abel
  · rw [hstate b (hac.trans hcb) le_rfl]
    by_cases hbc : b ≤ c
    · have h : b = c := le_antisymm hbc hcb
      simp only [X, if_pos hbc]
      calc
        _ = state c (state b η R.drift c) L.drift c := congrArg _ h
        _ = state b η R.drift c := L.endpoint
        _ = η := (congrArg (state b η R.drift) h.symm).trans R.endpoint
    · simpa only [X, if_neg hbc] using R.endpoint

end HeatBackwardCellGluing

#print axioms HeatBackwardCellGluing.glue
