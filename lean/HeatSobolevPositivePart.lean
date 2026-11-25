import EllipticPdes.Sobolev.GraphLattice

set_option autoImplicit false
noncomputable section

namespace HeatSobolevPositivePart

open EllipticPdes EllipticPdes.H1Graph Filter MeasureTheory Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem memFn (U : H1Graph μ Ω) : MemLp (fun x => max (fnL U x) 0) 2 (μ.restrict Ω) := by
  simpa only [sub_zero] using memLp_max_sub_const (Lp.memLp (fnL U)) (le_refl (0 : ℝ))

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem memGrad (U : H1Graph μ Ω) :
    MemLp (fun x => if 0 < fnL U x then gradL U x else 0) 2 (μ.restrict Ω) :=
  memLp_ite_lt_vec (Lp.memLp (fnL U)) (Lp.memLp (gradL U)) 0

def positivePart (U : H1Graph μ Ω) : H1Graph μ Ω :=
  H1Graph.mk ((memFn U).toLp _) ((memGrad U).toLp _)

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem fnL_positivePart (U : H1Graph μ Ω) :
    ⇑(fnL (positivePart U)) =ᵐ[μ.restrict Ω] fun x => max (fnL U x) 0 := by
  rw [positivePart, fnL_mk]
  exact (memFn U).coeFn_toLp

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem gradL_positivePart (U : H1Graph μ Ω) :
    ⇑(gradL (positivePart U)) =ᵐ[μ.restrict Ω] fun x => if 0 < fnL U x then gradL U x else 0 := by
  rw [positivePart, gradL_mk]
  exact (memGrad U).coeFn_toLp

theorem positivePart_mem_W12 (hΩ : IsOpen Ω) {U : H1Graph μ Ω} (hU : U ∈ W12 μ Ω) :
    positivePart U ∈ W12 μ Ω := by
  rw [mem_W12_iff_hasWeakFDerivOn hΩ]
  refine ((mem_W12_iff_hasWeakFDerivOn hΩ U).mp hU).posPart.congr_ae
    (fnL_positivePart U).symm ?_
  filter_upwards [gradL_positivePart U] with x h
  rw [h]
  split_ifs <;> simp

private theorem positivePart_tendsto_of_ae (hΩ : IsOpen Ω) {U : ℕ → H1Graph μ Ω} {V : H1Graph μ Ω}
    (hV : V ∈ W12 μ Ω) (h : Tendsto U atTop (𝓝 V))
    (hae : ∀ᵐ x ∂μ.restrict Ω, Tendsto (fun n => fnL (U n) x) atTop (𝓝 (fnL V x))) :
    Tendsto (fun n => positivePart (U n)) atTop (𝓝 (positivePart V)) := by
  obtain ⟨hf, hg⟩ := tendsto_iff.mp h
  have hf' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hf
  have hg' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hg
  refine tendsto_mk_of_tendsto_eLpNorm (memFn V) (memGrad V)
    (fun n => fnL_positivePart (U n)) (fun n => gradL_positivePart (U n)) ?_ ?_
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf'
      (fun _ => zero_le) (fun n => ?_)
    refine eLpNorm_mono_ae ((memFn (U n)).aestronglyMeasurable.sub (memFn V).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sub_zero] using abs_max_sub_le (fnL (U n) x) (fnL V x) 0
  · exact tendsto_eLpNorm_ite_lt_sub
      (fun n => (Lp.memLp (fnL (U n))).aestronglyMeasurable)
      (fun n => (Lp.memLp (gradL (U n))).aestronglyMeasurable)
      (Lp.memLp (fnL V)).aestronglyMeasurable (Lp.memLp (gradL V)) hg' hae
      (ae_gradL_eq_zero_of_fnL_eq hΩ hV 0)

theorem positivePart_tendsto (hΩ : IsOpen Ω) {U : ℕ → H1Graph μ Ω} {V : H1Graph μ Ω}
    (hV : V ∈ W12 μ Ω) (h : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => positivePart (U n)) atTop (𝓝 (positivePart V)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hsub := h.comp hns
  have hfn := (tendsto_iff.mp hsub).1
  have hlp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hfn
  obtain ⟨ms, hms, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hlp).exists_seq_tendsto_ae
  exact ⟨ms, positivePart_tendsto_of_ae hΩ hV (hsub.comp hms.tendsto_atTop) hae⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem positivePart_eq_zero {U : H1Graph μ Ω}
    (hU : ∀ᵐ x ∂μ.restrict Ω, fnL U x ≤ 0) : positivePart U = 0 := by
  apply H1Graph.ext
  · apply Lp.ext
    rw [map_zero]
    filter_upwards [fnL_positivePart U, hU, Lp.coeFn_zero ℝ 2 (μ.restrict Ω)] with x hx h h0
    exact (hx.trans (max_eq_right h)).trans h0.symm
  · apply Lp.ext
    rw [map_zero]
    filter_upwards [gradL_positivePart U, hU, Lp.coeFn_zero E 2 (μ.restrict Ω)] with x hx h h0
    exact (hx.trans (ite_eq_right (not_lt_of_ge h))).trans h0.symm

/-- A Sobolev graph with function part supported in a compact subset of the open
domain has zero boundary values. -/
theorem mem_H01_of_ae_compact (hΩ : IsOpen Ω) {V : H1Graph μ Ω} (hV : V ∈ W12 μ Ω)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hzero : ∀ᵐ x ∂μ.restrict Ω, x ∉ K → fnL V x = 0) : V ∈ H01 μ Ω := by
  classical
  let f : E → ℝ := K.indicator (fnL V)
  let g : E → E := K.indicator (gradL V)
  have hf : ⇑(fnL V) =ᵐ[μ.restrict Ω] f := by
    filter_upwards [hzero] with x hx
    by_cases hm : x ∈ K
    · simp [f, hm]
    · simp [f, hm, hx hm]
  have hg : ⇑(gradL V) =ᵐ[μ.restrict Ω] g := by
    filter_upwards [hzero, ae_gradL_eq_zero_of_fnL_eq hΩ hV 0] with x hx hz
    by_cases hm : x ∈ K
    · simp [g, hm]
    · simp [g, hm, hz (hx hm)]
  have hfg := ((mem_W12_iff_hasWeakFDerivOn hΩ V).mp hV).congr_ae hf
    (hg.mono fun x hx => congrArg (innerSL ℝ) hx)
  have htop : HasWeakFDerivOn ⊤ f (fun x => innerSL ℝ (g x)) μ :=
    hfg.top_of_forall_notMem_eq_zero hK hKΩ (fun x hx => indicator_of_notMem hx _)
      (fun x hx => by simp [g, hx])
  have hm := Measure.restrict_mono hKΩ (le_refl μ)
  have hfm : MemLp f 2 μ := (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).2
    ((Lp.memLp (fnL V)).mono_measure hm)
  have hgm : MemLp g 2 μ := (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).2
    ((Lp.memLp (gradL V)).mono_measure hm)
  have hfs : tsupport f ⊆ K := closure_minimal
    (fun x hx => by
      by_contra hn
      exact hx (indicator_of_notMem hn _)) hK.isClosed
  have hmem := mem_H01_of_hasCompactSupport hΩ htop hfm hgm
    (hK.of_isClosed_subset (isClosed_tsupport _) hfs) (hfs.trans hKΩ)
  have heq : H1Graph.mk ((hfm.mono_measure Measure.restrict_le_self).toLp f)
      ((hgm.mono_measure Measure.restrict_le_self).toLp g) = V := by
    apply H1Graph.ext
    · rw [fnL_mk]
      exact Lp.ext ((hfm.mono_measure Measure.restrict_le_self).coeFn_toLp.trans hf.symm)
    · rw [gradL_mk]
      exact Lp.ext ((hgm.mono_measure Measure.restrict_le_self).coeFn_toLp.trans hg.symm)
  rwa [heq] at hmem

/-- A nonnegative Sobolev function bounded above by a function in `H₀¹`
also has zero boundary values. -/
theorem mem_H01_of_nonnegative_le (hΩ : IsOpen Ω) {U V : H1Graph μ Ω} (hU : U ∈ H01 μ Ω)
    (hV : V ∈ W12 μ Ω) (hV0 : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ fnL V x)
    (hVU : ∀ᵐ x ∂μ.restrict Ω, fnL V x ≤ fnL U x) : V ∈ H01 μ Ω := by
  obtain ⟨φ, hφ⟩ := exists_seq_testGraphₗ_tendsto hU
  let A := fun n => positivePart (testGraphₗ μ Ω (φ n))
  let D := fun n => V - A n
  let W := fun n => V - positivePart (D n)
  have hA : Tendsto A atTop (𝓝 (positivePart U)) :=
    positivePart_tendsto hΩ (H01_le_W12 hU) hφ
  have hD : Tendsto D atTop (𝓝 (V - positivePart U)) := tendsto_const_nhds.sub hA
  have hlimit : positivePart (V - positivePart U) = 0 := by
    apply positivePart_eq_zero
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (fnL V) (fnL (positivePart U)), fnL_positivePart U, hVU]
      with x hx hy hz
    rw [hx, Pi.sub_apply, hy]
    exact sub_nonpos.mpr (hz.trans (le_max_left _ _))
  have hW : Tendsto W atTop (𝓝 V) := by
    simpa only [hlimit, sub_zero] using tendsto_const_nhds.sub
      (positivePart_tendsto hΩ ((W12 μ Ω).sub_mem hV (positivePart_mem_W12 hΩ (H01_le_W12 hU))) hD)
  refine isClosed_H01.mem_of_tendsto hW (Eventually.of_forall fun n => ?_)
  have hDn : D n ∈ W12 μ Ω := (W12 μ Ω).sub_mem hV
    (positivePart_mem_W12 hΩ (testGraphₗ_mem_W12 (φ n)))
  refine mem_H01_of_ae_compact hΩ ((W12 μ Ω).sub_mem hV (positivePart_mem_W12 hΩ hDn))
    (φ n).2.2.1 (φ n).2.2.2 ?_
  have hWrep : ⇑(fnL (W n)) =ᵐ[μ.restrict Ω]
      fun x => fnL V x - fnL (positivePart (D n)) x := by
    dsimp only [W]
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (fnL V) (fnL (positivePart (D n)))] with x hx
    simpa only [Pi.sub_apply] using hx
  have hDrep : ⇑(fnL (D n)) =ᵐ[μ.restrict Ω] fun x => fnL V x - fnL (A n) x := by
    dsimp only [D]
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (fnL V) (fnL (A n))] with x hx
    simpa only [Pi.sub_apply] using hx
  filter_upwards [hWrep, hDrep, fnL_positivePart (D n),
    fnL_positivePart (testGraphₗ μ Ω (φ n)), coeFn_fnL_testGraphₗ (φ n), hV0]
    with x hw hd hp ha htest hx hk
  have hz : (φ n : E → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport hk
  change fnL (A n) x = _ at ha
  rw [hw, hp, hd, ha, htest, hz, max_self, sub_zero, max_eq_left hx, sub_self]

end HeatSobolevPositivePart

#print axioms HeatSobolevPositivePart.positivePart_mem_W12
#print axioms HeatSobolevPositivePart.positivePart_tendsto
#print axioms HeatSobolevPositivePart.mem_H01_of_ae_compact
#print axioms HeatSobolevPositivePart.mem_H01_of_nonnegative_le
