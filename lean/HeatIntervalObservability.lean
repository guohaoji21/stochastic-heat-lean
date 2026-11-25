import HeatForwardNonzero
import HeatCanonicalPhysicalIto
import HeatCanonicalSeparable
import HeatSmallIntervalSmoothingComparison

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace HeatIntervalObservability

open MeasureTheory Filter Set SHE SHE.PredictableL2
open HeatIntervalNormalization HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open HeatConcreteSemigroupInput
open scoped NNReal ENNReal

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate

local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure; infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

/-- Every proposed constant in the squared observation estimate fails
on an actual backward mild solution with a Brownian-product terminal datum. -/
theorem exists_mild_counterexample (T : ℝ≥0) (hT : 0 < T) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1)
    (hbsupp : ∀ᵐ x ∂baseMeasure, x ∉ Ioo (6 : ℝ) 7 → b x = 0)
    (hbpos : ∀ᵐ x ∂baseMeasure, 0 ≤ b x)
    (hbone : ∀ x ∈ Ioo (25 / 4 : ℝ) (27 / 4), b x = 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgpos : ∀ x, 0 ≤ g x) (hgne : g ≠ 0)
    (hgsupp : tsupport g ⊆ Ioo (25 / 4 : ℝ) (27 / 4)) (hgmem : MemLp g 2 baseMeasure)
    (C : ℝ) (hC : 0 ≤ C) :
    letI : MeasurableSpace C(ℝ≥0, ℝ) :=
      HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∃ (t : ℕ → ℝ≥0) (N : ℕ), t 0 = 0 ∧ t N = T ∧
      (∀ n, n < N → t n < t (n + 1)) ∧
      Nonempty (HeatBackwardModel.Solution F μ T (noise b hb hbound)
        (HeatCanonicalPhysicalIto.integral T) W t N (hgmem.toLp g)) ∧
      (∀ ω, HeatBackwardModel.path T (noise b hb hbound) W t N (hgmem.toLp g) 0 ω =
        HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound)
          (fun k => t k - t (k - 1)) N (hgmem.toLp g) 0) ∧
      C * (∫ p : ℝ≥0 × C(ℝ≥0, ℝ), ‖paperBstar
        (HeatBackwardModel.path T (noise b hb hbound) W t N (hgmem.toLp g) p.1 p.2)‖ ^ 2
          ∂energyMeasure μ T) <
        ‖HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound)
          (fun k => t k - t (k - 1)) N (hgmem.toLp g) 0‖ ^ 2 := by
  letI : MeasurableSpace C(ℝ≥0, ℝ) :=
    HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : IsSeparable μ := HeatCanonicalSeparable.completed_separable
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  let G := hgmem.toLp g
  let J := HeatCanonicalNative.scalar T
  let I := HeatCanonicalPhysicalIto.integral T
  have hGpos : ∀ᵐ x ∂baseMeasure, 0 ≤ G x := by
    filter_upwards [hgmem.coeFn_toLp] with x hx
    rw [hx]
    exact hgpos x
  have hGplateau : ∀ᵐ x ∂baseMeasure, x ∉ HeatSubintervalMass.plateau → G x = 0 := by
    filter_upwards [hgmem.coeFn_toLp] with x hx hnot
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun hs => hnot (hgsupp hs))
  have hGne : G ≠ 0 := by
    intro hzero
    obtain ⟨a, d, δ, ha, had, hd, hδ, hpositive⟩ := HeatBarrierChoice.interval_inside hg hgpos hgne hgsupp
    have he : g =ᵐ[baseMeasure] (0 : ℝ → ℝ) := by
      have hgG : (G : ℝ → ℝ) =ᵐ[baseMeasure] g := hgmem.coeFn_toLp
      rw [hzero] at hgG
      exact hgG.symm.trans (Lp.coeFn_zero ℝ 2 baseMeasure)
    have hbad : ∀ᵐ x ∂baseMeasure, x ∉ Ioo a d := by
      filter_upwards [he] with x hx hinside
      have h := hpositive x ⟨hinside.1.le, hinside.2.le⟩
      rw [hx, Pi.zero_apply] at h
      exact (not_le_of_gt hδ) h
    have hm : baseMeasure (Ioo a d) = 0 := by
      simpa only [not_not, Set.setOf_mem_eq] using ae_iff.mp hbad
    have hsub : Ioo a d ⊆ Ioo (0 : ℝ) 10 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [baseMeasure, Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub, Real.volume_Ioo] at hm
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr had)).ne' hm
  let c := ‖HeatSmallIntervalSemigroup.smallHeat (T / 2) (HeatSubintervalMass.restrict G)‖ ^ 2
  have hc : 0 < c := (HeatSmallIntervalSmoothingComparison.paper_mass b hb hbound hbpos hbone
    G hGpos hGne hGplateau (fun _ => T) 1 T (by simp)).1
  have hGsupport : ∀ᵐ x ∂baseMeasure, x ∉ Ioo (6 : ℝ) 7 → G x = 0 := by
    filter_upwards [hgmem.coeFn_toLp] with x hx hnot
    rw [hx]
    apply image_eq_zero_of_notMem_tsupport
    intro hxg
    have hh := hgsupp hxg
    exact hnot ⟨by norm_num at hh ⊢; linarith [hh.1], by norm_num at hh ⊢; linarith [hh.2]⟩
  have hlim : Tendsto (fun n : ℕ =>
      (‖G‖ ^ 2 * C) * (2 * ‖G‖ ^ 2 * Real.exp (-4 * ((n : ℝ) + 1)))) atTop (nhds 0) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hneg := hnat.const_mul_atTop_of_neg (by norm_num : (-4 : ℝ) < 0)
    simpa using ((Real.tendsto_exp_atBot.comp hneg).const_mul (2 * ‖G‖ ^ 2)).const_mul (‖G‖ ^ 2 * C)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 _ (sq_pos_of_pos hc)).exists
  let L : ℝ := (n : ℝ) + 1
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨N, hN, hbefore, hend⟩ := HeatLogPartition.exists_partition L hL T hT
  let d := HeatLogPartition.lengths L hL
  let t := HeatClippedPartition.nodes d T
  have ht := HeatClippedPartition.nodes_mono d T
  have hprops := HeatClippedPartition.nodes_properties d T (HeatLogPartition.positive L hL) hN hbefore hend
  have hWa : ∀ a, StronglyMeasurable[F a] (W a) :=
    HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted
  have hP := HeatBrownianProducts.products_properties F μ T J (HeatCanonicalNative.locality T)
    W (HeatCanonicalNative.coordinate T) hWa t ht N (fun k _ => hprops.2.2.2 k)
  obtain ⟨back⟩ := HeatBackwardModel.exists_solution F μ T (noise b hb hbound) W t N G
    HeatCanonicalPhysicalIto.basis J (HeatCanonicalNative.locality T)
    (HeatCanonicalNative.coordinate T) hWa (fun ω => ω.continuous)
    ht hprops.1 hN hprops.2.2.1 hprops.2.1 hP
  have ht0 : t 0 = 0 := hprops.1
  have htN : t N = T := hprops.2.1
  refine ⟨t, N, ht0, htN, hprops.2.2.1, ⟨back⟩, ?_, ?_⟩
  · intro ω
    have hi := HeatBackwardProcess.initial family family_continuous family_contraction
      (noise b hb hbound) (H := T) W t ht N hN (hprops.2.2.1 0 (by omega)) htN.le G ω
    rw [ht0] at hi
    exact hi
  let q := HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) (fun k => t k - t (k - 1)) N G 0
  let obs := ∫ p : ℝ≥0 × C(ℝ≥0, ℝ),
    ‖paperBstar (HeatBackwardModel.path T (noise b hb hbound) W t N G p.1 p.2)‖ ^ 2 ∂energyMeasure μ T
  change C * obs < ‖q‖ ^ 2
  have hs := HeatClippedPartition.reverse_sum t ht N
  rw [ht0, htN, tsub_zero] at hs
  have hmassq : c ≤ inner ℝ G q := (HeatSmallIntervalSmoothingComparison.paper_mass b hb hbound hbpos hbone
    G hGpos hGne hGplateau (fun k => t k - t (k - 1)) N T hs).2
  have hcauchy := hmassq.trans (real_inner_le_norm G q)
  have hsq : c ^ 2 ≤ ‖G‖ ^ 2 * ‖q‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hc.le hcauchy 2
  have hobs : obs ≤ 2 * ‖G‖ ^ 2 * Real.exp (-4 * L) :=
    HeatLogObservation.bound F μ T J (HeatCanonicalNative.locality T) W
      (HeatCanonicalNative.coordinate T) hWa b hb hbound hbsupp L hL N hN hbefore hend G hGsupport I back
  by_contra! hbad
  have hmul := mul_le_mul_of_nonneg_left hbad (sq_nonneg ‖G‖)
  have hupper := mul_le_mul_of_nonneg_left hobs (mul_nonneg (sq_nonneg ‖G‖) hC)
  change (‖G‖ ^ 2 * C) * (2 * ‖G‖ ^ 2 * Real.exp (-4 * L)) < c ^ 2 at hn
  rw [← mul_assoc] at hmul
  exact (not_lt_of_ge (hsq.trans (hmul.trans hupper))) hn

end HeatIntervalObservability

#print axioms HeatIntervalObservability.exists_mild_counterexample
