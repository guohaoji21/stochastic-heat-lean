import HeatSmallIntervalEulerOrder
import HeatSobolevAffineGraph
import HeatSobolevDomainComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section

namespace HeatSmallIntervalSmoothingComparison

open EllipticPdes EllipticPdes.H1Graph MeasureTheory Set
open HeatIntervalNormalization HeatSmallIntervalSemigroup HeatSmallIntervalEulerOrder
open HeatSubintervalMass HeatSobolevIntervalMaps HeatSobolevAffineGraph
open scoped BigOperators NNReal RealInnerProductSpace

private abbrev I := HeatWeakDirichlet.domain
private abbrev J := plateau

private theorem restrict_transport (f : Base) :
    transportL2 (transport.symm (restrict f)) = restrictL2 plateau_subset_domain f := by
  rw [transportL2_apply, transport.apply_symm_apply]
  apply Lp.ext
  refine (normalizePlateau_ae (restrict f)).trans ?_
  exact ((HeatRestrictionAdjoint.restriction_ae baseMeasure plateau f).filter_mono
    (ae_mono (le_of_eq (nestedMeasure plateau_subset_domain).symm))).trans
    (restrictL2_ae plateau_subset_domain f).symm

private theorem extend_iso (f : SubintervalState) :
    extendL2 plateau_subset_domain (normalizePlateau f) = extend f := by
  apply Lp.ext
  have hiso := (normalizePlateau_ae f).filter_mono
    (ae_mono (le_of_eq (nestedMeasure plateau_subset_domain)))
  filter_upwards [extendL2_ae plateau_subset_domain measurableSet_Ioo (normalizePlateau f),
    HeatRestrictionAdjoint.adjointExtension_ae baseMeasure plateau measurableSet_Ioo f,
    (ae_restrict_iff' measurableSet_Ioo).mp hiso] with x hnew hold hx
  rw [hnew, hold]
  by_cases h : x ∈ plateau
  · simp only [indicator_of_mem h]
    exact hx h
  · rw [indicator_of_notMem h, indicator_of_notMem h]

/-- The actual implicit step on the plateau is dominated by the step on the
paper interval. The parameter is large enough that both normalized resolvents
are in the coercive range. -/
theorem smoothing_domination (a : ℝ) (ha : 400 ≤ a) (f : Base)
    (hf : ∀ᵐ x ∂baseMeasure, 0 ≤ f x) :
    ∀ᵐ x ∂baseMeasure, extend (smallSmoothing a ha (restrict f)) x ≤
      HeatDirichletResolvent.smoothing a (by linarith) f x := by
  let b := a / 400
  have hb : 1 ≤ b := by dsimp [b]; linarith
  have ha1 : 1 ≤ a := by linarith
  have hab : a = 400 * b := by dsimp [b]; ring
  let g := transport.symm (restrict f)
  let X := b • HeatDirichletResolventForm.lift b hb g
  let U : H01 volume J := ⟨toPlateau (X : Graph I), toPlateau_mem_H01 X.property⟩
  let V : H01 volume I := a • HeatDirichletResolventForm.lift a ha1 f
  have hV : fnL (V : Graph I) = HeatDirichletResolvent.smoothing a ha1 f := rfl
  have hU : fnL (U : Graph J) =
      normalizePlateau (smallSmoothing a ha (restrict f)) := by
    change fnL (toPlateau (X : Graph I)) = _
    rw [fnL_toPlateau, transportL2_apply, smallSmoothing_apply]
    rfl
  have hveq (W : H01 volume I) : a * inner ℝ (fnL (V : Graph I)) (fnL (W : Graph I)) +
      inner ℝ (gradL (V : Graph I)) (gradL (W : Graph I)) =
    inner ℝ (a • f) (fnL (W : Graph I)) := by
    have h := HeatDirichletResolventForm.variational ha1 f W
    change a * inner ℝ (fnL (HeatDirichletResolventForm.lift a ha1 f : Graph I)) (fnL (W : Graph I)) +
      inner ℝ (gradL (HeatDirichletResolventForm.lift a ha1 f : Graph I)) (gradL (W : Graph I)) =
      inner ℝ f (fnL (W : Graph I)) at h
    simp only [V, Submodule.coe_smul, map_smul, real_inner_smul_left]
    linear_combination a * h
  have hueq (W : H01 volume J) : a * inner ℝ (fnL (U : Graph J)) (fnL (W : Graph J)) +
      inner ℝ (gradL (U : Graph J)) (gradL (W : Graph J)) =
    inner ℝ (restrictL2 plateau_subset_domain (a • f)) (fnL (W : Graph J)) := by
    let W₀ : H01 volume I := ⟨fromPlateau (W : Graph J), fromPlateau_mem_H01 W.property⟩
    have hw : toPlateau (W₀ : Graph I) = (W : Graph J) := toPlateau_fromPlateau _
    have h := HeatDirichletResolventForm.variational hb g W₀
    change b * inner ℝ (fnL (HeatDirichletResolventForm.lift b hb g : Graph I)) (fnL (W₀ : Graph I)) +
      inner ℝ (gradL (HeatDirichletResolventForm.lift b hb g : Graph I)) (gradL (W₀ : Graph I)) =
      inner ℝ g (fnL (W₀ : Graph I)) at h
    have hr : transportL2 g = restrictL2 plateau_subset_domain f := restrict_transport f
    rw [← hw]
    change a * inner ℝ (fnL (toPlateau (X : Graph I))) (fnL (toPlateau (W₀ : Graph I))) +
      inner ℝ (gradL (toPlateau (X : Graph I))) (gradL (toPlateau (W₀ : Graph I))) = _
    rw [fnL_toPlateau, fnL_toPlateau, transportL2.inner_map_map, inner_grad_toPlateau,
      map_smul, ← hr, real_inner_smul_left, transportL2.inner_map_map, hab]
    simp only [X, Submodule.coe_smul, map_smul, real_inner_smul_left]
    linear_combination (400 * b) * h
  have hpos : ∀ᵐ x ∂volume.restrict I, 0 ≤ fnL (V : Graph I) x := by
    rw [hV]
    exact HeatResolventSpectrum.smoothing_nonnegative ha1 f hf
  have hc := HeatSobolevDomainComparison.extend_le_of_variational (I := I) (J := J) isOpen_Ioo isOpen_Ioo
    plateau_subset_domain (by linarith : 0 < a) (a • f) U V hpos hueq hveq
  change ∀ᵐ x ∂baseMeasure, extendL2 plateau_subset_domain (fnL (U : Graph J)) x ≤ fnL (V : Graph I) x at hc
  rwa [hU, extend_iso, hV] at hc

theorem heat_domination (t : ℝ≥0) (f : Base) (hf : ∀ᵐ x ∂baseMeasure, 0 ≤ f x) :
    ∀ᵐ x ∂baseMeasure, extend (smallHeat t (restrict f)) x ≤ paperHeat t f x :=
  heat_domination_of_smoothing smoothing_domination t f hf

theorem paper_mass (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (hbpos : ∀ᵐ x ∂baseMeasure, 0 ≤ b x)
    (hbone : ∀ x ∈ plateau, b x = 1) (g : Base)
    (hg : ∀ᵐ x ∂baseMeasure, 0 ≤ g x) (hne : g ≠ 0)
    (hsupp : ∀ᵐ x ∂baseMeasure, x ∉ plateau → g x = 0)
    (h : ℕ → ℝ≥0) (N : ℕ) (T : ℝ≥0) (hT : ∑ k ∈ Finset.range N, h (N - k) = T) :
    0 < ‖smallHeat (T / 2) (restrict g)‖ ^ 2 ∧
    ‖smallHeat (T / 2) (restrict g)‖ ^ 2 ≤
      inner ℝ g (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g 0) :=
  paper_mass_from_smoothing smoothing_domination b hb hbound hbpos hbone g hg hne hsupp h N T hT

end HeatSmallIntervalSmoothingComparison

#print axioms HeatSmallIntervalSmoothingComparison.smoothing_domination
#print axioms HeatSmallIntervalSmoothingComparison.heat_domination
#print axioms HeatSmallIntervalSmoothingComparison.paper_mass
