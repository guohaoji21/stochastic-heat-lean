import EllipticPdes.Extension.GraphOperator
import EllipticPdes.Extension.Patch
import EllipticPdes.Sobolev.H01Lattice
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 140000
noncomputable section

namespace HeatH01PositivePart

open Filter MeasureTheory Set EllipticPdes EllipticPdes.Sobolev EllipticPdes.Embedding
open EllipticPdes.Extension (hasWeakGradOn_of_mem_W12)
open scoped Topology

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}

/-- A weak graph whose coordinates vanish almost everywhere outside a
compact subset of the open set is a zero-boundary Sobolev graph. -/
theorem mem_H01_of_ae_support (ho : IsOpen U) (hb : Bornology.IsBounded U)
    {W : H1amb U} (hW : W ∈ W12 U)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hvanish : ∀ j : Fin (d + 1), ∀ᵐ x ∂volume.restrict U, x ∉ K → W j x = 0) :
    W ∈ H01 U := by
  obtain ⟨B, hBo, hKB, hBU, hBcompact⟩ := exists_open_between_and_isCompact_closure hK ho hKU
  obtain ⟨J, hJo, hKJ, hJB, _⟩ := exists_open_between_and_isCompact_closure hK hBo hKB
  obtain ⟨η, hη, _, hηsupp, hηone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hBo isClosed_closure hJB
  have hηts : tsupport η = closure B := by
    change closure (Function.support η) = closure B
    rw [hηsupp]
  have hηcs : HasCompactSupport η := by
    change IsCompact (tsupport η)
    rwa [hηts]
  have hval (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ K) : η x = 1 :=
    (hηone x).mp (subset_closure (hKJ hx))
  have hder (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ K) : partialD i η x = 0 := by
    have he : η =ᶠ[𝓝 x] (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) := by
      filter_upwards [hJo.mem_nhds (hKJ hx)] with y hy
      exact (hηone y).mp (subset_closure hy)
    rw [partialD_apply, he.fderiv_eq]
    simp
  let E (j : Fin (d + 1)) : EuclideanSpace ℝ (Fin d) → ℝ := U.indicator (fun x => W j x)
  let F (x : EuclideanSpace ℝ (Fin d)) := η x * E 0 x
  let G (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :=
    η x * E i.succ x + partialD i η x * E 0 x
  have hWm (j : Fin (d + 1)) : MemLp (fun x => W j x) 2 (volume.restrict U) := Lp.memLp _
  have hExt (j : Fin (d + 1)) : MemLp (E j) 2 volume :=
    (memLp_indicator_iff_restrict ho.measurableSet.nullMeasurableSet).2 (hWm j)
  have hF : F =ᵐ[volume] E 0 := by
    filter_upwards [(ae_restrict_iff' ho.measurableSet).mp (hvanish 0)] with x hx
    by_cases hu : x ∈ U
    · by_cases hk : x ∈ K
      · simp [F, hval x hk]
      · simp [F, E, indicator_of_mem hu, hx hu hk]
    · simp [F, E, indicator_of_notMem hu]
  have hG (i : Fin d) : G i =ᵐ[volume] E i.succ := by
    filter_upwards [(ae_restrict_iff' ho.measurableSet).mp (hvanish i.succ),
      (ae_restrict_iff' ho.measurableSet).mp (hvanish 0)] with x hx hx₀
    by_cases hu : x ∈ U
    · by_cases hk : x ∈ K
      · simp [G, hval x hk, hder i x hk]
      · simp [G, E, indicator_of_mem hu, hx hu hk, hx₀ hu hk]
    · simp [G, E, indicator_of_notMem hu]
  haveI := isFiniteMeasure_restrict_of_isBounded hb
  have hFin (j : Fin (d + 1)) : Integrable (fun x => W j x) (volume.restrict U) :=
    (hWm j).integrable one_le_two
  have hηU : tsupport η ⊆ U := by rwa [hηts]
  have hFw : HasWeakGradOn univ F G :=
    hasWeakGradOn_univ_mul_cutoff ho.measurableSet hη hηcs hηU
      (hFin 0) (fun k => hFin k.succ) (hasWeakGradOn_of_mem_W12 hW)
  have hFm : MemLp F 2 volume := (hExt 0).ae_eq hF.symm
  have hGm (i : Fin d) : MemLp (G i) 2 volume := (hExt i.succ).ae_eq (hG i).symm
  have hFts : tsupport F ⊆ tsupport η :=
    closure_mono (Function.support_mul_subset_left _ _)
  have hc := mem_H01_of_hasCompactSupport ho hFw hFm hGm hηcs.mul_right
    (hFts.trans hηU)
  convert hc using 1
  apply PiLp.ext
  intro j
  induction j using Fin.cases with
  | zero =>
    apply Lp.ext
    filter_upwards [((hFm.mono_measure Measure.restrict_le_self).coeFn_toLp),
      ae_restrict_of_ae hF, ae_restrict_mem ho.measurableSet] with x hx he hU
    exact ((hx.trans he).trans (indicator_of_mem hU _)).symm
  | succ i =>
    apply Lp.ext
    filter_upwards [((hGm i).mono_measure Measure.restrict_le_self).coeFn_toLp,
      ae_restrict_of_ae (hG i), ae_restrict_mem ho.measurableSet] with x hx he hU
    exact ((hx.trans he).trans (indicator_of_mem hU _)).symm

private def posFn (V : H1amb U) (x : EuclideanSpace ℝ (Fin d)) : ℝ := max (V 0 x) 0

private def posGrad (V : H1amb U) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if 0 < V 0 x then V i.succ x else 0

private theorem posFn_memLp (V : H1amb U) : MemLp (posFn V) 2 (volume.restrict U) := by
  change MemLp (fun x => max (V 0 x) 0) 2 (volume.restrict U)
  simpa only [sub_zero] using
    memLp_max_sub_const (Lp.memLp (V 0)) (k := 0) le_rfl

private theorem posGrad_memLp (V : H1amb U) (i : Fin d) : MemLp (posGrad V i) 2 (volume.restrict U) :=
  memLp_ite_lt_vec (Lp.memLp (V 0)) (Lp.memLp (V i.succ)) 0

private def posPart (V : H1amb U) : H1amb U :=
  WithLp.toLp 2 (Fin.cons ((posFn_memLp V).toLp (posFn V)) fun i =>
    (posGrad_memLp V i).toLp (posGrad V i))

private theorem pos_fn_ae (V : H1amb U) :
    (fun x => posPart V 0 x) =ᵐ[volume.restrict U] posFn V :=
  (posFn_memLp V).coeFn_toLp

private theorem pos_grad_ae (V : H1amb U) (i : Fin d) :
    (fun x => posPart V i.succ x) =ᵐ[volume.restrict U] posGrad V i :=
  (posGrad_memLp V i).coeFn_toLp

private theorem locInt (V : H1amb U) (j : Fin (d + 1)) :
    LocallyIntegrableOn (fun x => V j x) U volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp (V j)).locallyIntegrable one_le_two)

private theorem posPart_mem_W12 (ho : IsOpen U) (V : H1amb U) (hV : V ∈ W12 U) :
    posPart V ∈ W12 U :=
  EllipticPdes.Extension.mem_W12_of_hasWeakGradOn (posFn_memLp V) (posGrad_memLp V)
    (hasWeakGradOn_posPart ho (locInt V 0) (fun i => locInt V i.succ) (hasWeakGradOn_of_mem_W12 hV))

private theorem posPart_subseq (ho : IsOpen U) {V : H1amb U} (hV : V ∈ W12 U)
    (z : ℕ → H1amb U) (hz : Tendsto z atTop (𝓝 V)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (fun n => posPart (z (σ n))) atTop (𝓝 (posPart V)) := by
  have hcoe (j : Fin (d + 1)) : Tendsto (fun n => z n j) atTop (𝓝 (V j)) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => L2D U) j).continuousAt.tendsto.comp hz
  have hnorm (j : Fin (d + 1)) :
      Tendsto (fun n => eLpNorm (fun x => z n j x - V j x) 2 (volume.restrict U)) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 (hcoe j)
  obtain ⟨σ, hσ, hσae⟩ := (tendstoInMeasure_of_tendsto_Lp (hcoe 0)).exists_seq_tendsto_ae
  refine ⟨σ, hσ, ?_⟩
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => L2D U)).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro j
  induction j using Fin.cases with
  | zero =>
    change Tendsto (fun n => posPart (z (σ n)) 0) atTop (𝓝 (posPart V 0))
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2
    have ht : Tendsto (fun n => eLpNorm (posFn (z (σ n)) - posFn V) 2 (volume.restrict U))
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((hnorm 0).comp hσ.tendsto_atTop) (fun _ => zero_le) (fun n => ?_)
      apply eLpNorm_mono_ae
        ((posFn_memLp (z (σ n))).aestronglyMeasurable.sub (posFn_memLp V).aestronglyMeasurable)
      apply Eventually.of_forall
      intro x
      simpa only [Real.norm_eq_abs, Pi.sub_apply, posFn, sub_zero] using
        abs_max_sub_le (z (σ n) 0 x) (V 0 x) 0
    exact ht.congr fun n => eLpNorm_congr_ae
      ((pos_fn_ae (z (σ n))).symm.sub (pos_fn_ae V).symm)
  | succ i =>
    change Tendsto (fun n => posPart (z (σ n)) i.succ) atTop (𝓝 (posPart V i.succ))
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2
    have hlev : ∀ᵐ x ∂volume.restrict U, V 0 x = 0 → V i.succ x = 0 :=
      ae_eq_zero_of_eq_const_of_hasWeakGradOn ho (locInt V 0) (fun j => locInt V j.succ)
        (hasWeakGradOn_of_mem_W12 hV) 0 i
    have ht := tendsto_eLpNorm_ite_lt_sub (k := 0)
      (fun n => Lp.aestronglyMeasurable (z (σ n) 0))
      (fun n => Lp.aestronglyMeasurable (z (σ n) i.succ))
      (Lp.aestronglyMeasurable (V 0)) (Lp.memLp (V i.succ))
      ((hnorm i.succ).comp hσ.tendsto_atTop) hσae hlev
    exact ht.congr fun n => eLpNorm_congr_ae
      ((pos_grad_ae (z (σ n)) i).symm.sub (pos_grad_ae V i).symm)

private theorem test_sub_posPart_mem (ho : IsOpen U) (hb : Bornology.IsBounded U)
    {V : H1amb U} (hV : V ∈ W12 U) (hVpos : ∀ᵐ x ∂volume.restrict U, 0 ≤ V 0 x)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn U φ) : posPart (hφ.testGraph - V) ∈ H01 U := by
  let z := hφ.testGraph - V
  have hz : z ∈ W12 U := (W12 U).sub_mem (testGraph_mem_W12 hφ) hV
  apply mem_H01_of_ae_support ho hb (posPart_mem_W12 ho z hz) hφ.2.1 hφ.2.2
  have hzero : ∀ᵐ x ∂volume.restrict U, x ∉ tsupport φ → z 0 x ≤ 0 := by
    have hz₀ : z 0 = hφ.testCls - V 0 := by simp [z]
    rw [hz₀]
    filter_upwards [Lp.coeFn_sub hφ.testCls (V 0), hφ.memLp.coeFn_toLp, hVpos] with x hsub hfn hp hx
    rw [show (hφ.testCls - V 0) x = _ from hsub, Pi.sub_apply, show hφ.testCls x = φ x from hfn,
      image_eq_zero_of_notMem_tsupport hx, zero_sub]
    exact neg_nonpos.mpr hp
  intro j
  induction j using Fin.cases with
  | zero =>
    filter_upwards [pos_fn_ae z, hzero] with x hx hz hxK
    rw [hx, posFn, max_eq_right (hz hxK)]
  | succ i =>
    filter_upwards [pos_grad_ae z i, hzero] with x hx hz hxK
    rw [hx, posGrad, ite_eq_right (not_lt.mpr (hz hxK))]

/-- The positive difference from a nonnegative ambient weak Sobolev
function is an admissible zero-boundary test. -/
theorem exists_positive_sub (ho : IsOpen U) (hb : Bornology.IsBounded U) (u : H01 U)
    (V : H1amb U) (hV : V ∈ W12 U) (hVpos : ∀ᵐ x ∂volume.restrict U, 0 ≤ V 0 x) :
    ∃ w : H01 U, (fun x => (w : H1amb U) 0 x) =ᵐ[volume.restrict U]
        (fun x => max (((u : H1amb U) 0) x - V 0 x) 0) ∧
      ∀ i : Fin d, (fun x => (w : H1amb U) i.succ x) =ᵐ[volume.restrict U]
        (fun x => if V 0 x < ((u : H1amb U) 0) x then
          ((u : H1amb U) i.succ) x - V i.succ x else 0) := by
  let z := (u : H1amb U) - V
  have hz : z ∈ W12 U := (W12 U).sub_mem (H01_le_W12 U u.2) hV
  have hu : (u : H1amb U) ∈ closure (testGraphSet U) := by rw [← coe_H01]; exact u.2
  obtain ⟨ψ, hψ, hψlim⟩ := mem_closure_iff_seq_limit.mp hu
  obtain ⟨σ, _, hlim⟩ := posPart_subseq ho hz (fun n => ψ n - V) (hψlim.sub_const V)
  have hw : posPart z ∈ H01 U := by
    have hclosed : IsClosed ((H01 U : Set (H1amb U))) := by rw [coe_H01]; exact isClosed_closure
    apply hclosed.mem_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    obtain ⟨φ, hφ, he⟩ := hψ (σ n)
    rw [he]
    exact test_sub_posPart_mem ho hb hV hVpos hφ
  refine ⟨⟨posPart z, hw⟩, ?_, ?_⟩
  · filter_upwards [pos_fn_ae z, Lp.coeFn_sub ((u : H1amb U) 0) (V 0)] with x h₁ h₂
    have h₃ : z 0 x = ((u : H1amb U) 0) x - V 0 x := h₂
    rw [h₁, posFn, h₃]
  · intro i
    filter_upwards [pos_grad_ae z i, Lp.coeFn_sub ((u : H1amb U) 0) (V 0),
      Lp.coeFn_sub ((u : H1amb U) i.succ) (V i.succ)] with x h₁ h₂ h₃
    have h₄ : z 0 x = ((u : H1amb U) 0) x - V 0 x := h₂
    have h₅ : z i.succ x = ((u : H1amb U) i.succ) x - V i.succ x := h₃
    simp only [h₁, posGrad, h₄, h₅, sub_pos]

end HeatH01PositivePart

#print axioms HeatH01PositivePart.mem_H01_of_ae_support
#print axioms HeatH01PositivePart.exists_positive_sub
