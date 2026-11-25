import HeatTorusDaviesGaffney

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusPaperDaviesGaffney

open MeasureTheory Set Filter UnitAddTorus HeatTorusReal HeatRestrictionAdjoint
open HeatTorusInitialData (rescale)
open HeatFlatTorusDistance (distance)
open scoped NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι]

/-- Distance between two sets in the flat geodesic distance. -/
def setDistance {P : ℝ} (A D : Set (ι → AddCircle P)) : ℝ :=
  sInf ((fun p => distance p.1 p.2) '' (A ×ˢ D))

theorem setDistance_le {P : ℝ} {A D : Set (ι → AddCircle P)}
    {x y : ι → AddCircle P} (hx : x ∈ A) (hy : y ∈ D) :
    setDistance A D ≤ distance x y := by
  refine csInf_le ⟨0, ?_⟩ ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  rintro _ ⟨p, _, rfl⟩
  exact norm_nonneg _

/-- Multiplication by the indicator of a measurable subset, as a map on the
ambient real state space. -/
def indicatorMultiplier (D : Set (UnitAddTorus ι)) : RealState ι →L[ℝ] RealState ι :=
  (adjointExtension volume D).comp (restriction volume D)

theorem indicatorMultiplier_ae {D : Set (UnitAddTorus ι)} (hD : MeasurableSet D)
    (f : RealState ι) : (indicatorMultiplier D f : UnitAddTorus ι → ℝ) =ᵐ[volume] D.indicator f := by
  filter_upwards [adjointExtension_ae volume D hD (restriction volume D f),
    (ae_restrict_iff' hD).mp (restriction_ae volume D f)] with x he hr
  change adjointExtension volume D (restriction volume D f) x = D.indicator f x
  rw [he]
  by_cases hx : x ∈ D
  · simp only [indicator_of_mem hx, hr hx]
  · simp only [indicator_of_notMem hx]

/-- The paper's operator norm inequality with the distance between the
physical observation and support sets and prefactor one. -/
theorem operator_norm {P : ℝ} (hP : 0 < P) (A D : Set (ι → AddCircle P))
    (hA : MeasurableSet A) (hD : MeasurableSet D) (hAn : A.Nonempty) (hDn : D.Nonempty)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ‖((restriction volume (rescale hP ⁻¹' A)).comp (realHeat P t)).comp
        (indicatorMultiplier (rescale hP ⁻¹' D))‖ ≤
      Real.exp (-setDistance A D ^ 2 / (4 * (t : ℝ))) := by
  classical
  let z := setDistance A D
  let S := rescale hP ⁻¹' A
  let V := rescale hP ⁻¹' D
  have hs : MeasurableSet S := hA.preimage (rescale hP).continuous.measurable
  have hv : MeasurableSet V := hD.preimage (rescale hP).continuous.measurable
  have hnonneg (p : (ι → AddCircle P) × (ι → AddCircle P)) : 0 ≤ distance p.1 p.2 :=
    norm_nonneg _
  have hz : 0 ≤ z := by
    apply le_csInf ((hAn.prod hDn).image _)
    rintro _ ⟨p, _, rfl⟩
    exact hnonneg p
  have hsep (x : UnitAddTorus ι) (hx : x ∈ S) (y : ι → AddCircle P) (hy : y ∈ D) :
      z ≤ distance (rescale hP x) y :=
    setDistance_le (show rescale hP x ∈ A from hx) hy
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro f
  have ha := indicatorMultiplier_ae hv f
  have hsupp : ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)),
      rescale hP x ∉ D → indicatorMultiplier V f x = 0 := by
    filter_upwards [ha] with x hx h
    rw [hx, indicator_of_notMem (show x ∉ V from h)]
  have hnorm : ‖indicatorMultiplier V f‖ ≤ ‖f‖ := by
    rw [← one_mul ‖f‖]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [ha] with x hx
    rw [hx, one_mul]
    by_cases hm : x ∈ V
    · rw [indicator_of_mem hm]
    · rw [indicator_of_notMem hm, norm_zero]
      exact norm_nonneg _
  exact (HeatTorusDaviesGaffney.restriction_heat hP hz S hs D hsep t ht _ hsupp).trans
    (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)

/-- The sharp observation bound for heat durations in `[0,L]`, including
the zero-duration endpoint of the covariance integral. -/
theorem supported_time_bound {P δ r L : ℝ} (hP : 0 < P) (hδ : 0 < δ)
    (hL : 0 < L) (hr : 0 ≤ r) (hrL : r ≤ L)
    (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ distance (rescale hP x) (rescale hP y))
    (f : RealState ι) (hf : ∀ᵐ x ∂volume, x ∉ D → f x = 0) :
    ‖restriction volume O (realHeat P r f)‖ ≤ Real.exp (-(δ ^ 2 / 4) / L) * ‖f‖ := by
  classical
  rcases hr.eq_or_lt with he | ht
  · subst r
    rw [realHeat_zero, ContinuousLinearMap.id_apply]
    have hz : restriction volume O f = 0 := by
      apply Lp.ext
      filter_upwards [restriction_ae volume O f, ae_restrict_of_ae hf, ae_restrict_mem hO,
        Lp.coeFn_zero ℝ 2 ((volume : Measure (UnitAddTorus ι)).restrict O)] with x hr hs hx hz
      have hnot : x ∉ D := by
        intro hxD
        have h := hsep x hx x hxD
        have he : distance (rescale hP x) (rescale hP x) = 0 := by
          simp [HeatFlatTorusDistance.distance_eq_sqrt]
        linarith
      rw [hr, hs hnot, hz, Pi.zero_apply]
    rw [hz, norm_zero]
    positivity
  · let E := rescale hP '' D
    have hs (x : UnitAddTorus ι) (hx : x ∈ O) (y : ι → AddCircle P) (hy : y ∈ E) :
        δ ≤ distance (rescale hP x) y := by
      obtain ⟨z, hz, rfl⟩ := hy
      exact hsep x hx z hz
    have hsupp : ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), rescale hP x ∉ E → f x = 0 := by
      filter_upwards [hf] with x hx hn
      exact hx (fun h => hn (mem_image_of_mem (rescale hP) h))
    have hb := HeatTorusDaviesGaffney.restriction_heat hP hδ.le O hO E hs
      (⟨r, hr⟩ : ℝ≥0) ht f hsupp
    refine hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    change -δ ^ 2 / (4 * r) ≤ -(δ ^ 2 / 4) / L
    rw [neg_div, neg_div, div_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left hrL (by norm_num)))

end HeatTorusPaperDaviesGaffney

#print axioms HeatTorusPaperDaviesGaffney.indicatorMultiplier_ae
#print axioms HeatTorusPaperDaviesGaffney.operator_norm
#print axioms HeatTorusPaperDaviesGaffney.supported_time_bound
