import HeatTorusFixedBarrier
import HeatTorusInitialData

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace HeatTorusGevreyData

open MeasureTheory Set UnitAddTorus HeatTorusReal HeatTorusInitialData HeatTorusCovarianceSeparation
open scoped NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ℝ}

/-- The coefficient and initial state are independent of the final time.
The spatial support and the positive pairing are in the same normalized
coordinates as the observation estimate. -/
structure Data (hP : 0 < P) (s : ℝ) (O : Set (ι → AddCircle P)) where
  coefficient : (ι → AddCircle P) → ℝ
  initial : (ι → AddCircle P) → ℝ
  rate : ℝ
  rate_pos : 0 < rate
  coefficient_smooth : ContDiff ℝ (⊤ : ℕ∞) (coefficient ∘ HeatTorusGevreyCutoff.chart 0)
  coefficient_bounds : ∀ (l : List ι) x,
    ‖HeatGevreyProduct.mixedPartial l (coefficient ∘ HeatTorusGevreyCutoff.chart 0) x‖ ≤
      rate ^ l.length * (l.length.factorial : ℝ) ^ s
  coefficient_range : ∀ x, coefficient x ∈ Icc 0 1
  initial_smooth : ContDiff ℝ (⊤ : ℕ∞) (initial ∘ HeatTorusGevreyCutoff.chart 0)
  initial_value : RealState ι
  initial_ae : (initial_value : UnitAddTorus ι → ℝ) =ᵐ[volume] initial ∘ rescale hP
  initial_ne : initial_value ≠ 0
  multiplier : RealState ι →L[ℝ] RealState ι
  multiplier_apply : ∀ v : RealState ι, (fun x => multiplier v x) =ᵐ[volume]
    fun x => coefficient (rescale hP x) * v x
  multiplier_norm : ‖multiplier‖ ≤ 1
  multiplier_symm : ∀ x y, inner ℝ (multiplier x) y = inner ℝ x (multiplier y)
  support : Set (UnitAddTorus ι)
  gap : ℝ
  gap_pos : 0 < gap
  separated : ∀ x ∈ rescale hP ⁻¹' O, ∀ y ∈ support, gap ≤ dist x y
  multiplier_support : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ support → multiplier v x = 0
  initial_support : ∀ᵐ x ∂volume, x ∉ support → initial_value x = 0
  uniform_pairing : ∀ T : ℝ≥0, ∃ a : ℝ, 0 < a ∧
    ∀ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t → t 0 = 0 → t N = T →
      a ≤ inner ℝ initial_value (HeatBackwardChain.stateAt (K P multiplier)
        (fun j => t j - t (j - 1)) N initial_value 0)

theorem exists_data_from_cutoff (hP : 0 < P) {s : ℝ}
    {U O : Set (ι → AddCircle P)} (hU : IsOpen U) (hdisj : Disjoint U O)
    (b g : (ι → AddCircle P) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hb : Continuous b) (hg : Continuous g) (hb01 : ∀ x, b x ∈ Icc 0 1)
    (hbreg : ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0))
    (hbgev : ∀ (l : List ι) x,
      ‖HeatGevreyProduct.mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x‖ ≤
        ρ ^ l.length * (l.length.factorial : ℝ) ^ s)
    (hgreg : ContDiff ℝ (⊤ : ℕ∞) (g ∘ HeatTorusGevreyCutoff.chart 0))
    (D : Set (UnitAddTorus ι)) (hD : IsCompact (closure D))
    (hDU : closure D ⊆ rescale hP ⁻¹' U) (hbD : rescale hP ⁻¹' tsupport b ⊆ D)
    (c : ι → AddCircle P) (hg1 : g c = 1) (hb1 : ∀ x ∈ tsupport g, b x = 1)
    (hpair : ∀ (M : RealState ι →L[ℝ] RealState ι) (G : RealState ι), G ≠ 0 →
      (G : UnitAddTorus ι → ℝ) =ᵐ[volume] g ∘ rescale hP →
      (∀ v : RealState ι, (fun x => M v x) =ᵐ[volume] fun x => b (rescale hP x) * v x) →
      ∀ T : ℝ≥0, ∃ a : ℝ, 0 < a ∧
        ∀ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t → t 0 = 0 → t N = T →
          a ≤ inner ℝ G (HeatBackwardChain.stateAt (K P M) (fun j => t j - t (j - 1)) N G 0)) :
    ∃ d : Data hP s O, d.coefficient = b ∧ d.initial = g ∧ d.support = D := by
  obtain ⟨M, G, hM, hGne, _, hG, hGsupp, hMv⟩ := exists_multiplier_and_initial hP b g hb hg hb01 c hg1 hb1
  let q := rescale (ι := ι) hP
  let V := q ⁻¹' U
  have hV : IsOpen V := hU.preimage q.continuous
  obtain ⟨δ, hδ, hsep⟩ := Metric.exists_pos_forall_lt_edist hD hV.isClosed_compl
    (disjoint_left.mpr fun x hx hy => hy (hDU hx))
  refine ⟨⟨b, g, ρ, hρ, hbreg, hbgev, hb01, hgreg, G, hG, hGne, M, hMv, hM,
    ?_, D, δ, by exact_mod_cast hδ, ?_, ?_, ?_, hpair M G hGne hG hMv⟩, rfl, rfl, rfl⟩
  · intro u v
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hMv u, hMv v] with x hu hv
    rw [hu, hv, Real.inner_apply, Real.inner_apply]
    ring
  · intro x hx y hy
    have hnot : x ∈ Vᶜ := fun hxV => disjoint_left.mp hdisj hxV hx
    have h := hsep y (subset_closure hy) x hnot
    rw [edist_nndist, ENNReal.coe_lt_coe] at h
    simpa only [dist_comm] using (show (δ : ℝ) ≤ dist y x by exact_mod_cast h.le)
  · intro v
    filter_upwards [hMv v] with x hx hn
    rw [hx, image_eq_zero_of_notMem_tsupport (fun hs => hn (hbD hs)), zero_mul]
  · filter_upwards [hGsupp] with x hx hn
    exact hx (fun hgx => hn (hbD (subset_tsupport b (show b (q x) ≠ 0 by
      rw [hb1 (q x) hgx]
      norm_num))))

theorem exists_data (hP : 0 < P) {s : ℝ} (hs : 1 < s)
    {U O : Set (ι → AddCircle P)} (hU : IsOpen U) (hdisj : Disjoint U O)
    (c : ι → AddCircle P) (hc : c ∈ U) : Nonempty (Data hP s O) := by
  obtain ⟨b, g, ρ, hρ, hb, hg, hbreg, hbgev, hb01, hg01, hbcp, _, hgreg, hg1, hb1, _, hbU, _⟩ :=
    HeatTorusGevreyCutoff.exists_cutoff_and_initial hP hs hU hdisj c hc
  let q := rescale (ι := ι) hP
  let D := q ⁻¹' tsupport b
  have hDclosed : IsClosed D := isClosed_closure.preimage q.continuous
  have hD : IsCompact (closure D) := by
    rw [hDclosed.closure_eq, show D = q.symm '' tsupport b from (congrFun q.image_symm (tsupport b)).symm]
    exact hbcp.image q.symm.continuous
  have hDU : closure D ⊆ q ⁻¹' U := by
    rw [hDclosed.closure_eq]
    exact preimage_mono hbU
  obtain ⟨d, _, _, _⟩ := exists_data_from_cutoff hP hU hdisj b g ρ hρ hb hg hb01 hbreg hbgev
    hgreg D hD hDU Subset.rfl c hg1 hb1 (by
    intro M G _ hG hMv T
    have hpos : HeatTorusMass.Positive M := by
      intro v hv
      filter_upwards [hMv v, hv] with x hx hy
      rw [hx]
      exact mul_nonneg (hb01 _).1 hy
    exact HeatTorusFixedBarrier.uniform_pairing P (b ∘ q) (g ∘ q) (hg.comp q.continuous)
      (fun x => (hg01 (q x)).1) (q.symm c) (by simp [hg1])
      (fun x hx => hb1 (q x) (subset_tsupport g hx)) M hpos hMv G hG T)
  exact ⟨d⟩

end HeatTorusGevreyData

#print axioms HeatTorusGevreyData.exists_data
