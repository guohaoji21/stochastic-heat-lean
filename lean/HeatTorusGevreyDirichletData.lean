import HeatTorusDirichletBall
import HeatTorusGevreyData
import HeatClippedPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace HeatTorusGevreyDirichletData

open Filter MeasureTheory Set UnitAddTorus
open HeatFlatTorusSmoothLift (covering covering_surjective covering_isOpenMap covering_isQuotientMap)
open HeatTorusReal HeatTorusInitialData HeatTorusCovarianceSeparation
open scoped NNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {n : ℕ} {P s : ℝ}

private theorem pairing (hP : 0 < P) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r < 1/2)
    (b g : (Fin n → AddCircle P) → ℝ) (hb : Continuous b)
    (hbpos : ∀ z, 0 ≤ b z) (hgpos : ∀ z, 0 ≤ g z)
    (hplateau : ∀ z ∈ (rescale hP ∘ covering 1) '' Metric.ball x r, b z = 1)
    (hgsupp : tsupport g ⊆ (rescale hP ∘ covering 1) '' Metric.ball x r)
    (M : RealState (Fin n) →L[ℝ] RealState (Fin n)) (G : RealState (Fin n)) (hGne : G ≠ 0)
    (hG : (G : UnitAddTorus (Fin n) → ℝ) =ᵐ[volume] g ∘ rescale hP)
    (hM : ∀ v : RealState (Fin n), (fun y => M v y) =ᵐ[volume] fun y => b (rescale hP y) * v y)
    (T : ℝ≥0) :
    ∃ a : ℝ, 0 < a ∧ ∀ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t → t 0 = 0 → t N = T →
      a ≤ inner ℝ G (HeatBackwardChain.stateAt (K P M) (fun j => t j - t (j - 1)) N G 0) := by
  let w : C(UnitAddTorus (Fin n), ℝ) := ⟨b ∘ rescale hP, hb.comp (rescale hP).continuous⟩
  have hMw : M = HeatTorusSmoothWeight.weight w := by
    ext v : 1
    apply Lp.ext
    exact (hM v).trans (HeatTorusSmoothWeight.weight_ae w v).symm
  subst M
  have hwpos (y : UnitAddTorus (Fin n)) : 0 ≤ w y := hbpos _
  have hwplateau (y : UnitAddTorus (Fin n)) (hy : y ∈ covering 1 '' Metric.ball x r) : w y = 1 := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact hplateau _ (mem_image_of_mem (rescale hP ∘ covering 1) hz)
  have hGpos : ∀ᵐ y ∂volume, 0 ≤ G y := by
    filter_upwards [hG] with y hy
    rw [hy]
    exact hgpos _
  have hGsupp : ∀ᵐ y ∂volume, y ∉ covering 1 '' Metric.ball x r → G y = 0 := by
    filter_upwards [hG] with y hy hnot
    rw [hy]
    change g (rescale hP y) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    obtain ⟨z, hz, he⟩ := hgsupp hs
    exact hnot ⟨z, hz, (rescale hP).injective he⟩
  let cT := ‖HeatSmallDomainDirichletHeat.heat Metric.isOpen_ball Metric.isBounded_ball
      ((T / 2) / Real.toNNReal (P ^ 2))
      (HeatTorusPatchSobolev.pull (HeatTorusDirichletBall.cellOrigin x)
        (HeatTorusDirichletBall.ball_subset_cell x hr) (HeatTorusDirichletBall.measurable_image_ball x hr) G)‖ ^ 2
  have hpos : 0 < cT :=
    (HeatTorusDirichletBall.initial_pairing_ball P x hr w hwpos hwplateau (fun _ => T) 1 T
      (by simp) G hGpos hGne hGsupp).1
  refine ⟨cT, hpos, fun t N ht ht0 htN => ?_⟩
  have hsum := HeatClippedPartition.reverse_sum t ht N
  rw [ht0, htN, tsub_zero] at hsum
  exact (HeatTorusDirichletBall.initial_pairing_ball P x hr w hwpos hwplateau
    (fun j => t j - t (j - 1)) N T hsum G hGpos hGne hGsupp).2

/-- The coefficient is supported in a coordinate ball inside the gap.
The initial state is supported in a smaller coordinate ball, on which the
coefficient is identically one. The uniform pairing uses its Dirichlet flow. -/
theorem exists_data (hP : 0 < P) (hs : 1 < s)
    {U O : Set (Fin n → AddCircle P)} (hU : IsOpen U) (hdisj : Disjoint U O)
    (c : Fin n → AddCircle P) (hc : c ∈ U) :
    ∃ (x : EuclideanSpace ℝ (Fin n)) (r R : ℝ), 0 < r ∧ r < R ∧ R < 1/2 ∧
      (rescale hP ∘ covering 1) x = c ∧ (rescale hP ∘ covering 1) '' Metric.closedBall x R ⊆ U ∧
      ∃ d : HeatTorusGevreyData.Data hP s O,
        d.support = covering 1 '' Metric.ball x R ∧
        closure ((rescale hP ∘ covering 1) '' Metric.ball x r) ⊆
          (rescale hP ∘ covering 1) '' Metric.ball x R ∧
        tsupport d.coefficient ⊆ (rescale hP ∘ covering 1) '' Metric.ball x R ∧
        tsupport d.initial ⊆ (rescale hP ∘ covering 1) '' Metric.ball x r ∧
        (∀ y ∈ (rescale hP ∘ covering 1) '' Metric.closedBall x r, d.coefficient y = 1) ∧
        ∀ y, 0 ≤ d.initial y := by
  let q := rescale (ι := Fin n) hP
  let e : EuclideanSpace ℝ (Fin n) → (Fin n → AddCircle P) := q ∘ covering 1
  have he : Continuous e := q.continuous.comp (covering_isQuotientMap 1).continuous
  have heOpen : IsOpenMap e := q.isOpenMap.comp (covering_isOpenMap 1)
  obtain ⟨x, hx⟩ := (q.surjective.comp (covering_surjective 1)) c
  have hxc : e x = c := hx
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage he).mem_nhds (show e x ∈ U from hxc.symm ▸ hc))
  let R := min (1/4) (ε/2)
  have hR : 0 < R := lt_min (by norm_num) (by positivity)
  have hRsmall : R < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  have hRε : R < ε := (min_le_right _ _).trans_lt (by linarith)
  have houter : e '' Metric.closedBall x R ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hεU (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt hRε))
  let D := e '' Metric.ball x R
  have hD : IsOpen D := heOpen (Metric.ball x R) Metric.isOpen_ball
  have hcD : c ∈ D := ⟨x, Metric.mem_ball_self hR, hx⟩
  obtain ⟨b, ρ, hρ, hb, hbD, _, hb01, hb1, hbreg, hbgev⟩ :=
    HeatTorusGevreyCutoff.exists_cutoff_in_open hP hs hD c hcD
  obtain ⟨V, hVone, hVopen, hcV⟩ := mem_nhds_iff.mp hb1
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.mp
    ((hVopen.preimage he).mem_nhds (show e x ∈ V from hxc.symm ▸ hcV))
  let r := min (R/2) (η/2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r < R := (min_le_left _ _).trans_lt (by linarith)
  have hrη : r < η := (min_le_right _ _).trans_lt (by linarith)
  have hplateau : ∀ y ∈ e '' Metric.closedBall x r, b y = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hVone (hηV (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt hrη)))
  let A := e '' Metric.ball x r
  have hA : IsOpen A := heOpen (Metric.ball x r) Metric.isOpen_ball
  have hcA : c ∈ A := ⟨x, Metric.mem_ball_self hr, hx⟩
  obtain ⟨g, _, _, hg, hgA, _, hg01, hg1, hgreg, _⟩ :=
    HeatTorusGevreyCutoff.exists_cutoff_in_open hP hs hA c hcA
  have hbA : ∀ y ∈ A, b y = 1 := fun y hy => hplateau y (image_mono Metric.ball_subset_closedBall hy)
  let D₀ := covering 1 '' Metric.ball x R
  have hcompact := (isCompact_closedBall x R).image (covering_isQuotientMap 1).continuous
  have hclosure : closure D₀ ⊆ covering 1 '' Metric.closedBall x R :=
    closure_minimal (image_mono Metric.ball_subset_closedBall) hcompact.isClosed
  have hgap : closure D₀ ⊆ q ⁻¹' U := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hclosure hy
    exact houter (mem_image_of_mem e hz)
  have hbD₀ : q ⁻¹' tsupport b ⊆ D₀ := by
    intro y hy
    obtain ⟨z, hz, heq⟩ := hbD hy
    exact ⟨z, hz, q.injective heq⟩
  obtain ⟨d, hdb, hdg, hdD⟩ := HeatTorusGevreyData.exists_data_from_cutoff hP hU hdisj b g ρ hρ hb hg hb01
    hbreg hbgev hgreg D₀ (hcompact.of_isClosed_subset isClosed_closure hclosure) hgap hbD₀ c
    hg1.self_of_nhds (fun y hy => hbA y (hgA hy))
    (pairing hP x (hrR.trans hRsmall) b g hb (fun y => (hb01 y).1) (fun y => (hg01 y).1) hbA hgA)
  have hnested : closure A ⊆ D :=
    (closure_minimal (image_mono Metric.ball_subset_closedBall) ((isCompact_closedBall x r).image he).isClosed).trans
      (image_mono (Metric.closedBall_subset_ball hrR))
  refine ⟨x, r, R, hr, hrR, hRsmall, hx, houter, d, hdD, hnested, ?_⟩
  simpa only [hdb, hdg] using
    (show tsupport b ⊆ D ∧ tsupport g ⊆ A ∧
      (∀ y ∈ e '' Metric.closedBall x r, b y = 1) ∧ ∀ y, 0 ≤ g y from
      ⟨hbD, hgA, hplateau, fun y => (hg01 y).1⟩)

end HeatTorusGevreyDirichletData

#print axioms HeatTorusGevreyDirichletData.exists_data
