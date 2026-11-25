import HeatTorusDirichletDomination
import HeatTorusMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace HeatTorusDirichletMass

open Filter MeasureTheory Set UnitAddTorus EllipticPdes.Sobolev
open HeatTorusReal HeatTorusPatchSobolev
open HeatFlatTorusSmoothLift (covering)
open HeatTorusFundamentalCell (cell patchEquiv patch_measurePreserving
  representative representative_measurePreserving covering_representative)
open HeatRestrictionAdjoint (restriction adjointExtension)
open scoped RealInnerProductSpace NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
variable (a : Fin d → ℝ) (hU : U ⊆ cell a) (hm : MeasurableSet (covering 1 '' U))
  (ho : IsOpen U) (hb : Bornology.IsBounded U)

abbrev PatchState (U : Set (EuclideanSpace ℝ (Fin d))) :=
  Lp ℝ 2 ((volume : Measure (UnitAddTorus (Fin d))).restrict (covering 1 '' U))

private theorem patchEquiv_nonnegative (f : PatchState U)
    (hf : ∀ᵐ x ∂volume.restrict (covering 1 '' U), 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict U, 0 ≤ patchEquiv a hU ho.measurableSet hm f x := by
  have hc := patch_measurePreserving a hU hm
  filter_upwards [Lp.coeFn_compMeasurePreserving f hc, hc.quasiMeasurePreserving.ae hf] with x hx hy
  change 0 ≤ Lp.compMeasurePreserving (covering 1) hc f x
  rwa [hx]

private theorem patchEquiv_symm_nonnegative (f : L2D U)
    (hf : ∀ᵐ x ∂volume.restrict U, 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict (covering 1 '' U), 0 ≤ (patchEquiv a hU ho.measurableSet hm).symm f x := by
  let e := patchEquiv a hU ho.measurableSet hm
  let g := e.symm f
  have hc := patch_measurePreserving a hU hm
  have hr := representative_measurePreserving a hU ho.measurableSet hm
  have he := Lp.coeFn_compMeasurePreserving g hc
  change ((e g : L2D U) : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict U] g ∘ covering 1 at he
  rw [e.apply_symm_apply f] at he
  have hloc : ∀ᵐ x ∂volume.restrict U, 0 ≤ g (covering 1 x) := by
    filter_upwards [hf, he] with x h₁ h₂
    change f x = g (covering 1 x) at h₂
    rwa [← h₂]
  filter_upwards [hr.quasiMeasurePreserving.ae hloc] with x hx
  change 0 ≤ g (covering 1 (representative a x)) at hx
  rwa [covering_representative] at hx

/-- The Euclidean Dirichlet heat semigroup transported to the patch,
with physical time for the specified torus period. -/
def patchHeat (P : ℝ) (t : ℝ≥0) : PatchState U →L[ℝ] PatchState U :=
  let e := patchEquiv a hU ho.measurableSet hm
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((HeatSmallDomainDirichletHeat.heat ho hb (t / Real.toNNReal (P ^ 2))).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap)

theorem patchHeat_apply (P : ℝ) (t : ℝ≥0) (f : PatchState U) :
    patchHeat a hU hm ho hb P t f =
      (patchEquiv a hU ho.measurableSet hm).symm
        (HeatSmallDomainDirichletHeat.heat ho hb (t / Real.toNNReal (P ^ 2))
          (patchEquiv a hU ho.measurableSet hm f)) := rfl

theorem patchHeat_nonnegative (P : ℝ) (t : ℝ≥0) (f : PatchState U)
    (hf : ∀ᵐ x ∂volume.restrict (covering 1 '' U), 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict (covering 1 '' U), 0 ≤ patchHeat a hU hm ho hb P t f x := by
  rw [patchHeat_apply]
  exact patchEquiv_symm_nonnegative a hU hm ho _
    (HeatSmallDomainDirichletHeat.heat_nonnegative ho hb _ _ (patchEquiv_nonnegative a hU hm ho f hf))

theorem patchHeat_add (P : ℝ) (s t : ℝ≥0) (f : PatchState U) :
    patchHeat a hU hm ho hb P (s + t) f =
      patchHeat a hU hm ho hb P s (patchHeat a hU hm ho hb P t f) := by
  simp only [patchHeat_apply, add_div, HeatSmallDomainDirichletHeat.heat_add,
    ContinuousLinearMap.comp_apply, LinearIsometryEquiv.apply_symm_apply]

theorem patchHeat_zero (P : ℝ) (f : PatchState U) : patchHeat a hU hm ho hb P 0 f = f := by
  simp only [patchHeat_apply, zero_div, HeatSmallDomainDirichletHeat.heat_zero,
    ContinuousLinearMap.id_apply, LinearIsometryEquiv.symm_apply_apply]

theorem patchHeat_inner_symm (P : ℝ) (t : ℝ≥0) (f g : PatchState U) :
    ⟪patchHeat a hU hm ho hb P t f, g⟫ = ⟪f, patchHeat a hU hm ho hb P t g⟫ := by
  let e := patchEquiv a hU ho.measurableSet hm
  let S := HeatSmallDomainDirichletHeat.heat ho hb (t / Real.toNNReal (P ^ 2))
  change ⟪e.symm (S (e f)), g⟫ = ⟪f, e.symm (S (e g))⟫
  rw [← e.inner_map_map (e.symm (S (e f))) g, ← e.inner_map_map f (e.symm (S (e g))),
    e.apply_symm_apply, e.apply_symm_apply]
  exact HeatSmallDomainDirichletHeat.heat_inner_symm ho hb _ _ _

theorem patchHeat_injective (P : ℝ) (t : ℝ≥0) :
    Function.Injective (patchHeat a hU hm ho hb P t) :=
  (patchEquiv a hU ho.measurableSet hm).symm.injective.comp
    ((HeatSmallDomainDirichletHeat.heat_injective ho hb _).comp
      (patchEquiv a hU ho.measurableSet hm).injective)

theorem patchHeat_domination (P : ℝ) (t : ℝ≥0) (f : RealState (Fin d))
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, adjointExtension volume (covering 1 '' U)
        (patchHeat a hU hm ho hb P t (restriction volume (covering 1 '' U) f)) x ≤ realHeat P t f x :=
  HeatTorusDirichletDomination.heat_domination_physical a hU hm ho hb P t f hf

/-- The lower bound in the initial pairing is the square of the exact
Dirichlet heat norm at the midpoint. -/
theorem initial_pairing_dirichlet (P : ℝ) (M : RealState (Fin d) →L[ℝ] RealState (Fin d))
    (hM : HeatTorusMass.Positive M)
    (hfixed : ∀ f : PatchState U, M (adjointExtension volume (covering 1 '' U) f) =
      adjointExtension volume (covering 1 '' U) f)
    (h : ℕ → ℝ≥0) (N : ℕ) (T : ℝ≥0) (hT : ∑ k ∈ Finset.range N, h (N - k) = T)
    (g : RealState (Fin d)) (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (hg₀ : g ≠ 0)
    (hsupp : ∀ᵐ x ∂volume, x ∉ covering 1 '' U → g x = 0) :
    let c := ‖HeatSmallDomainDirichletHeat.heat ho hb ((T / 2) / Real.toNNReal (P ^ 2))
        (pull a hU hm g)‖ ^ 2
    0 < c ∧ c ≤ ⟪g, HeatBackwardChain.stateAt (HeatTorusCovarianceSeparation.K P M) h N g 0⟫ := by
  have hlow := HeatTorusMass.initial_pairing_domain_comparison hm P M hM hfixed
    (patchHeat a hU hm ho hb P) (patchHeat_nonnegative a hU hm ho hb P)
    (patchHeat_add a hU hm ho hb P) (patchHeat_domination a hU hm ho hb P)
    (patchHeat_zero a hU hm ho hb P) (patchHeat_inner_symm a hU hm ho hb P)
    h N T hT (patchHeat_injective a hU hm ho hb P (T / 2)) g hg hg₀ hsupp
  have he :
      ‖patchHeat a hU hm ho hb P (T / 2) (restriction volume (covering 1 '' U) g)‖ =
        ‖HeatSmallDomainDirichletHeat.heat ho hb ((T / 2) / Real.toNNReal (P ^ 2))
          (pull a hU hm g)‖ := by
    rw [patchHeat_apply]
    exact (patchEquiv a hU ho.measurableSet hm).symm.norm_map _
  rw [he] at hlow
  exact hlow

end HeatTorusDirichletMass

#print axioms HeatTorusDirichletMass.patchHeat_domination
#print axioms HeatTorusDirichletMass.initial_pairing_dirichlet
