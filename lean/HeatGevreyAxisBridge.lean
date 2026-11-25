import HeatGevreyOneUniqueness
import HeatTorusAxisFourier

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace HeatGevreyAxisBridge

open Set Topology HeatGevreyProduct HeatGevreyOneUniqueness HeatTorusAxisFourier
open HeatTorusGaussian (wrap continuous_wrap)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem contDiff_update (x : ι → ℝ) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Function.update x i t) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    have he : (fun t : ℝ => Function.update x i t i) = id := by
      funext t
      exact Function.update_self i t x
    rw [he]
    exact contDiff_id
  · simpa only [Function.update_of_ne hj] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => x j))

private theorem coordinateDeriv_eq (f : (ι → ℝ) → ℝ) (hf : Differentiable ℝ f)
    (i : ι) (x : ι → ℝ) : coordinateDeriv i f x = fderiv ℝ f x (Pi.single i 1) := by
  have path (t : ℝ) : Function.update x i t = x + (t - x i) • (Pi.single i 1 : ι → ℝ) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [Function.update_self, Pi.single_eq_same]
    · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  have hd := (((hasDerivAt_id (x i)).sub_const (x i)).smul_const (Pi.single i (1 : ℝ))).const_add x
  have hpath : HasDerivAt (fun t : ℝ => Function.update x i t) (Pi.single i 1) (x i) := by
    simpa only [path, id_eq, one_smul] using hd
  have hx : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self]
    exact (hf x).hasFDerivAt
  have h := hx.comp_hasDerivAt (x i) hpath
  exact h.deriv

private theorem contDiff_mixedPartial (l : List ι) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (mixedPartial l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    have hd := ih.differentiable (Ne.symm (ENat.natCast_ne_coe_top 0))
    have he : mixedPartial (i :: l) f = fun x => fderiv ℝ (mixedPartial l f) x (Pi.single i 1) :=
      funext (coordinateDeriv_eq _ hd i)
    rw [he]
    exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

private theorem wrap_surjective : Function.Surjective (wrap (ι := ι)) := by
  intro x
  choose y hy using fun i : ι =>
    (QuotientAddGroup.mk_surjective : Function.Surjective (fun t : ℝ => (t : UnitAddCircle))) (x i)
  exact ⟨y, funext hy⟩

theorem wrap_isQuotientMap : IsQuotientMap (wrap (ι := ι)) := by
  have he : wrap (ι := ι) = HeatTorusGevreyCutoff.chart (0 : UnitAddTorus ι) := by
    funext x
    rw [HeatTorusGevreyCutoff.chart, zero_add]
    rfl
  have ho : IsOpenMap (wrap (ι := ι)) := by
    rw [he]
    exact HeatTorusGevreyCutoff.isOpenMap_chart (0 : UnitAddTorus ι)
  exact ho.isQuotientMap continuous_wrap wrap_surjective

private def axisFun (b : UnitAddTorus ι → ℝ) (i : ι) (x : UnitAddTorus ι) (t : ℝ) : ℝ :=
  b (x + Pi.single i (t : UnitAddCircle))

private def jet (b : UnitAddTorus ι → ℝ) (i : ι) (n : ℕ) (x : UnitAddTorus ι) : ℝ :=
  iteratedDeriv n (axisFun b i x) 0

private theorem axisFun_wrap (b : UnitAddTorus ι → ℝ) (i : ι) (x : ι → ℝ) :
    axisFun b i (wrap x) = fun t => (b ∘ wrap) (Function.update x i (t + x i)) := by
  funext t
  apply congrArg b
  funext j
  by_cases hj : j = i
  · subst j
    simp [wrap, Pi.single_eq_same, AddCircle.coe_add, add_comm]
  · simp [wrap, Pi.single_eq_of_ne hj, Function.update_of_ne hj]

private theorem jet_wrap (b : UnitAddTorus ι → ℝ) (i : ι) (n : ℕ) (x : ι → ℝ) :
    jet b i n (wrap x) = mixedPartial (List.replicate n i) (b ∘ wrap) x := by
  rw [jet, axisFun_wrap,
    iteratedDeriv_comp_add_const n (fun u => (b ∘ wrap) (Function.update x i u)) (x i)]
  simp only [zero_add, iteratedDeriv_section, Function.update_eq_self]

private theorem contDiff_axisFun (b : UnitAddTorus ι → ℝ) (i : ι)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b ∘ wrap)) (x : UnitAddTorus ι) :
    ContDiff ℝ (⊤ : ℕ∞) (axisFun b i x) := by
  obtain ⟨v, rfl⟩ := wrap_surjective x
  rw [axisFun_wrap]
  exact (hb.comp (contDiff_update v i)).comp (contDiff_id.add contDiff_const)

private theorem jet_shift (b : UnitAddTorus ι → ℝ) (i : ι) (n : ℕ) (x : UnitAddTorus ι) (t : ℝ) :
    jet b i n (x + Pi.single i (t : UnitAddCircle)) = iteratedDeriv n (axisFun b i x) t := by
  have he : axisFun b i (x + Pi.single i (t : UnitAddCircle)) = fun u => axisFun b i x (u + t) := by
    funext u
    apply congrArg b
    funext j
    by_cases hj : j = i
    · subst j
      simp [Pi.single_eq_same, AddCircle.coe_add, add_comm u t, add_assoc]
    · simp [Pi.single_eq_of_ne hj]
  rw [jet, he, iteratedDeriv_comp_add_const]
  simp only [zero_add]

/-- The derivative hypotheses in the torus Fourier decay theorem follow from
the Euclidean mixed-partial bounds on the actual periodic lift. -/
theorem coefficient_decay [Nonempty ι] (b : UnitAddTorus ι → ℝ) (C ρ : ℝ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hb : ContDiff ℝ (⊤ : ℕ∞) (b ∘ wrap))
    (hD : ∀ (l : List ι) x, |mixedPartial l (b ∘ wrap) x| ≤
      C * ρ ^ l.length * (l.length.factorial : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ι → ℤ,
      ‖UnitAddTorus.mFourierCoeff (fun x => (b x : ℂ)) k‖ ≤
        2 * C * Real.exp (-a * ∑ i, |(k i : ℝ)|) := by
  let f : ι → ℕ → UnitAddTorus ι → ℂ := fun i n x => (jet b i n x : ℂ)
  refine exponential_decay (fun x => (b x : ℂ)) f ?_ ?_ ?_ C ρ hC hρ ?_
  · intro i
    funext x
    simp [f, jet, axisFun, iteratedDeriv_zero]
  · intro i n
    apply Complex.continuous_ofReal.comp
    apply wrap_isQuotientMap.continuous_iff.mpr
    have he : jet b i n ∘ wrap = mixedPartial (List.replicate n i) (b ∘ wrap) := funext (jet_wrap b i n)
    rw [he]
    exact (contDiff_mixedPartial _ hb).continuous
  · intro i n x t
    have hs := contDiff_axisFun b i hb x
    have hd := ((hs.differentiable_iteratedDeriv n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) t).hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    simpa only [f, sectionAt, jet_shift] using hd.ofReal_comp
  · intro i n x
    obtain ⟨v, rfl⟩ := wrap_surjective x
    simpa only [f, Complex.norm_real, Real.norm_eq_abs, jet_wrap, List.length_replicate] using
      hD (List.replicate n i) v

end HeatGevreyAxisBridge

#print axioms HeatGevreyAxisBridge.coefficient_decay
