import HeatGevreyPeriodization
import HeatGevreyProduct
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
noncomputable section

namespace HeatTorusGevreyCutoff

open Set Filter HeatGevreyProduct HeatGevreyPeriodization
open scoped Topology

variable {ι : Type*} {P : ℝ}

def chart (c : ι → AddCircle P) (x : ι → ℝ) : ι → AddCircle P :=
  c + fun i => (x i : AddCircle P)

theorem chart_zero (c : ι → AddCircle P) : chart c 0 = c := by
  simp [chart, ← Pi.zero_def]

theorem continuous_chart (c : ι → AddCircle P) : Continuous (chart c) :=
  continuous_const.add (continuous_pi fun i => (AddCircle.continuous_mk' P).comp (continuous_apply i))

theorem isOpenMap_chart (c : ι → AddCircle P) : IsOpenMap (chart c) := by
  have hcoe : IsOpenMap (fun x : ℝ => (x : AddCircle P)) := QuotientAddGroup.isOpenMap_coe
  have hsurj : Function.Surjective (fun x : ℝ => (x : AddCircle P)) := QuotientAddGroup.mk_surjective
  exact (Homeomorph.addLeft c).isOpenMap.comp (IsOpenMap.piMap (fun _ => hcoe) (Eventually.of_forall fun _ => hsurj))

private theorem coe_representative (hP : 0 < P) (x : ℝ) :
    ((toIcoMod hP (-P/2) x : ℝ) : AddCircle P) = (x : AddCircle P) := by
  have h := congrArg (fun t : ℝ => (t : AddCircle P)) (toIcoMod_add_toIcoDiv_zsmul hP (-P/2) x)
  simpa only [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero] using h

variable [Fintype ι] [DecidableEq ι]

/-- Every open neighborhood on the period-`P` torus contains the support
of a Gevrey cutoff that is one on a neighborhood of its center. Smoothness
and the mixed partial bounds are stated on the periodic Euclidean lift. -/
theorem exists_cutoff_in_open (hP : 0 < P) {s : ℝ} (hs : 1 < s)
    {U : Set (ι → AddCircle P)} (hU : IsOpen U) (c : ι → AddCircle P) (hc : c ∈ U) :
    ∃ b : (ι → AddCircle P) → ℝ, ∃ ρ : ℝ, 0 < ρ ∧ Continuous b ∧
      tsupport b ⊆ U ∧ HasCompactSupport b ∧ (∀ x, b x ∈ Set.Icc 0 1) ∧
      (∀ᶠ x in 𝓝 c, b x = 1) ∧ ContDiff ℝ (⊤ : ℕ∞) (b ∘ chart 0) ∧
      ∀ (l : List ι) x, ‖mixedPartial l (b ∘ chart 0) x‖ ≤ ρ ^ l.length * (l.length.factorial : ℝ) ^ s := by
  letI : Fact (0 < P) := ⟨hP⟩
  have hpre : chart c ⁻¹' U ∈ 𝓝 (0 : ι → ℝ) := by
    have ht := (continuous_chart c).continuousAt (x := 0)
    rw [ContinuousAt, chart_zero] at ht
    exact ht.eventually (hU.mem_nhds hc)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let R := min (P/4) (ε/2)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRP : R < P/2 := (min_le_left _ _).trans_lt (by linarith)
  have hRε : R < ε := (min_le_right _ _).trans_lt (by linarith)
  let r := R/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  obtain ⟨f, ρ, hρ, hfper, hfreg, hf01, hf1, hf0, hfD⟩ :=
    exists_periodic_cutoff hP hs hr hrR hRP
  let g : AddCircle P → ℝ := hfper.lift
  have hg_coe (t : ℝ) : g (t : AddCircle P) = f t := hfper.lift_coe t
  have hg : Continuous g := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hfreg.continuous
  let b : (ι → AddCircle P) → ℝ := fun x => ∏ i, g (x i - c i)
  have hb_chart : b ∘ chart c = product (fun _ => f) := by
    funext x
    dsimp only [Function.comp_apply, b, chart, product, Pi.add_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [add_comm (c i), add_sub_cancel_right, hg_coe]
  have hsurj : Function.Surjective (fun x : ℝ => (x : AddCircle P)) := QuotientAddGroup.mk_surjective
  choose v hv using fun i : ι => hsurj (c i)
  have hb_lift : b ∘ chart 0 = product (fun i t => f (t-v i)) := by
    funext x
    dsimp only [Function.comp_apply, b, chart, product, Pi.add_apply, Pi.zero_apply, zero_add]
    apply Finset.prod_congr rfl
    intro i _
    simp only [zero_add, ← hv i, ← AddCircle.coe_sub, hg_coe]
  let K : Set (ι → ℝ) := Set.pi univ (fun _ => Set.Icc (-R) R)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hK_U : chart c '' K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    have hd : dist x 0 ≤ R := (dist_pi_le_iff hR.le).mpr fun i => by
      simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using abs_le.mpr (hx i (mem_univ i))
    exact hball (hd.trans_lt hRε)
  have hK' := hK.image (continuous_chart c)
  have hbK : tsupport b ⊆ chart c '' K := by
    apply closure_minimal _ hK'.isClosed
    intro x hx
    have hcoord (i : ι) : ∃ t : ℝ, t ∈ Set.Icc (-R) R ∧ (t : AddCircle P) = x i - c i := by
      obtain ⟨y, hy⟩ := hsurj (x i - c i)
      have hg_ne : g (y : AddCircle P) ≠ 0 := by
        intro hzero
        apply hx
        change (∏ j, g (x j - c j)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hy ▸ hzero)
      refine ⟨toIcoMod hP (-P/2) y, abs_le.mp (le_of_lt ?_), (coe_representative hP y).trans hy⟩
      exact lt_of_not_ge fun h => hg_ne ((hg_coe y).trans (hf0 y h))
    choose y hy hy' using hcoord
    refine ⟨y, fun i _ => hy i, ?_⟩
    funext i
    change c i + (y i : AddCircle P) = x i
    rw [hy', add_comm, sub_add_cancel]
  refine ⟨b, ρ, hρ, ?_, hbK.trans hK_U, hK'.of_isClosed_subset isClosed_closure hbK,
    ?_, ?_, ?_, ?_⟩
  · apply continuous_finsetProd
    intro i _
    exact hg.comp ((continuous_apply i).sub continuous_const)
  · intro x
    apply product_mem_Icc (g := fun i (_ : ℝ) => g (x i - c i)) (x := fun _ => 0)
    intro i _
    obtain ⟨y, hy⟩ := hsurj (x i - c i)
    rw [← hy, hg_coe]
    exact hf01 y
  · let V : Set (ι → ℝ) := Set.pi univ (fun _ => Set.Ioo (-r) r)
    have hV : IsOpen V := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
    have hmem : c ∈ chart c '' V := ⟨0, fun i _ => ⟨by simpa using neg_lt_zero.mpr hr, by simpa using hr⟩, chart_zero c⟩
    filter_upwards [(isOpenMap_chart c V hV).mem_nhds hmem] with x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have each (i : ι) : f (y i) = 1 := hf1 _ (abs_lt.mpr (hy i (mem_univ i))).le
    have he := congrFun hb_chart y
    simpa [Function.comp_apply, product, each] using he
  · rw [hb_lift]
    exact contDiff_product _ (fun _ => hfreg.comp (contDiff_id.sub contDiff_const))
  · rw [hb_lift]
    apply mixedPartial_bound (by linarith) hρ
    intro i n x
    rw [iteratedDeriv_comp_sub_const]
    exact hfD n _

/-- Choose the coefficient and the nonzero initial state before any final
time or control is fixed. The initial state is supported on the coefficient's
unit plateau, and the coefficient has positive distance from the control set. -/
theorem exists_cutoff_and_initial (hP : 0 < P) {s : ℝ} (hs : 1 < s)
    {U G₀ : Set (ι → AddCircle P)} (hU : IsOpen U) (hdisj : Disjoint U G₀)
    (c : ι → AddCircle P) (hc : c ∈ U) :
    ∃ b g : (ι → AddCircle P) → ℝ, ∃ ρ : ℝ, 0 < ρ ∧ Continuous b ∧ Continuous g ∧
      ContDiff ℝ (⊤ : ℕ∞) (b ∘ chart 0) ∧
      (∀ (l : List ι) x, ‖mixedPartial l (b ∘ chart 0) x‖ ≤ ρ ^ l.length * (l.length.factorial : ℝ) ^ s) ∧
      (∀ x, b x ∈ Set.Icc 0 1) ∧ (∀ x, g x ∈ Set.Icc 0 1) ∧
      HasCompactSupport b ∧ HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) (g ∘ chart 0) ∧
      g c = 1 ∧ (∀ x ∈ tsupport g, b x = 1) ∧ tsupport g ⊆ U ∧ tsupport b ⊆ U ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport b, ∀ y ∈ G₀, δ < dist x y := by
  obtain ⟨b, ρ, hρ, hb, hbU, hbcp, hb01, hb1, hbD, hbG⟩ := exists_cutoff_in_open hP hs hU c hc
  obtain ⟨V, hVsub, hVopen, hcV⟩ := mem_nhds_iff.mp hb1
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hVopen
  obtain ⟨g, _, _, hg, hgW, hgcp, hg01, hg1, hgD, _⟩ := exists_cutoff_in_open hP hs hW c ⟨hc, hcV⟩
  refine ⟨b, g, ρ, hρ, hb, hg, hbD, hbG, hb01, hg01, hbcp, hgcp, hgD,
    hg1.self_of_nhds, (fun x hx => hVsub (hgW hx).2), (fun x hx => (hgW hx).1), hbU, ?_⟩
  have hsep : Disjoint (tsupport b) Uᶜ := disjoint_left.mpr fun x hx hxc => hxc (hbU hx)
  obtain ⟨δ, hδ, hdist⟩ := Metric.exists_pos_forall_lt_edist hbcp hU.isClosed_compl hsep
  refine ⟨δ, by exact_mod_cast hδ, fun x hx y hy => ?_⟩
  have hyU : y ∈ Uᶜ := fun h => disjoint_left.mp hdisj h hy
  have hxy := hdist x hx y hyU
  rw [edist_nndist, ENNReal.coe_lt_coe] at hxy
  exact_mod_cast hxy

end HeatTorusGevreyCutoff

#print axioms HeatTorusGevreyCutoff.exists_cutoff_in_open
#print axioms HeatTorusGevreyCutoff.exists_cutoff_and_initial
