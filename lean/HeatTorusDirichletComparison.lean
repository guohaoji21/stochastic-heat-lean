import HeatTorusDirichletExtension
import HeatTorusResolventForm
import HeatH01PositivePart
import HeatSmallDomainDirichletHeat
import HeatTorusEuler

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace HeatTorusDirichletComparison

open Filter MeasureTheory Set UnitAddTorus EllipticPdes EllipticPdes.Sobolev
open HeatTorusReal HeatTorusPatchSobolev
open HeatFlatTorusSmoothLift (covering)
open HeatTorusFundamentalCell (cell patch_measurePreserving representative
  representative_measurePreserving covering_representative)
open HeatTorusDirichletExtension (pull_push push_gradient)
open scoped RealInnerProductSpace NNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
variable (a : Fin d → ℝ) (hU : U ⊆ cell a)
  (hm : MeasurableSet (covering 1 '' U))

theorem pull_nonnegative (f : RealState (Fin d)) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict U, 0 ≤ pull a hU hm f x := by
  have hc := patch_measurePreserving a hU hm
  filter_upwards [pull_ae a hU hm f, hc.quasiMeasurePreserving.ae (ae_restrict_of_ae hf)]
    with x hx hn
  rw [hx]
  exact hn

/-- An order bound on a patch transports back to the torus by zero
extension, provided the ambient function is nonnegative. -/
theorem push_le (hUm : MeasurableSet U) (g : L2D U) (f : RealState (Fin d))
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (h : ∀ᵐ x ∂volume.restrict U, g x ≤ pull a hU hm f x) :
    ∀ᵐ x ∂volume, push a hU hm hUm g x ≤ f x := by
  let S := covering 1 '' U
  let p := push a hU hm hUm g
  have hr := representative_measurePreserving a hU hUm hm
  have hg := pull_ae a hU hm p
  rw [show pull a hU hm p = g from pull_push a hU hm hUm g] at hg
  have hloc : ∀ᵐ x ∂volume.restrict U, p (covering 1 x) ≤ f (covering 1 x) := by
    filter_upwards [h, hg, pull_ae a hU hm f] with x hx h₁ h₂
    rwa [h₁, h₂] at hx
  have ht : ∀ᵐ x ∂volume.restrict S, p x ≤ f x := by
    filter_upwards [hr.quasiMeasurePreserving.ae hloc] with x hx
    change p (covering 1 (representative a x)) ≤ f (covering 1 (representative a x)) at hx
    rwa [covering_representative] at hx
  filter_upwards [(ae_restrict_iff' hm).mp ht, push_ae a hU hm hUm g, hf] with x hx hp hn
  by_cases hs : x ∈ S
  · exact hx hs
  · rw [hp, indicator_of_notMem hs]
    exact hn

/-- In local coordinates, the ambient torus resolvent solves the same
weak equation as the Dirichlet resolvent against every zero-boundary test. -/
theorem torus_resolvent_on_patch (hUm : MeasurableSet U) (s : ℝ≥0) (hs : 0 < s)
    (f : RealState (Fin d)) :
    ∃ V : H1amb U, V ∈ W12 U ∧
      V 0 = pull a hU hm (HeatTorusResolvent.step 1 s f) ∧
      ∀ v : H01 U, ⟪V 0, (v : H1amb U) 0⟫ +
        (s : ℝ) * ∑ i : Fin d, ⟪V i.succ, H01.grad v i⟫ =
          ⟪pull a hU hm f, (v : H1amb U) 0⟫ := by
  let u := HeatTorusResolvent.step 1 s f
  obtain ⟨D, hD, hw⟩ := HeatTorusResolventForm.variational_real_tests 1 s hs f
  let V := graph a hU hm (embed u) D
  have hv₀ : V 0 = pull a hU hm u := by
    change pull a hU hm (realPart (embed u)) = _
    rw [realPart_embed]
  refine ⟨V, graph_mem_W12 a hU hm _ D hD, hv₀, ?_⟩
  intro v
  have h := hw (push a hU hm hUm ((v : H1amb U) 0))
    (fun i => push a hU hm hUm (H01.grad v i)) (push_gradient a hU hm hUm v)
  rw [hv₀]
  change ⟪pull a hU hm u, (v : H1amb U) 0⟫ +
    (s : ℝ) * ∑ i : Fin d, ⟪pull a hU hm (realPart (D i)), H01.grad v i⟫ = _
  simp_rw [pull_push_pairing a hU hm hUm]
  exact h

private theorem inner_sub_eq_sq_of_mask (u v w : L2D U)
    (h : ∀ᵐ x ∂volume.restrict U, w x = u x - v x ∨ w x = 0) :
    ⟪u, w⟫ - ⟪v, w⟫ = ‖w‖ ^ 2 := by
  rw [← inner_sub_left, ← real_inner_self_eq_norm_sq, L2.real_inner_eq_integral,
    L2.real_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [h, Lp.coeFn_sub u v] with x hx hsub
  rw [show (u - v) x = u x - v x from hsub]
  rcases hx with he | he
  · rw [← he]
  · simp [he]

private theorem torus_step_zero (f : RealState (Fin d)) : HeatTorusResolvent.step 1 0 f = f := by
  apply (Function.LeftInverse.injective (realPart_embed (ι := Fin d)))
  apply (mFourierBasis (d := Fin d)).repr.injective
  apply lp.ext
  funext k
  simp only [mFourierBasis_repr, HeatTorusResolvent.coefficient_step, NNReal.coe_zero,
    zero_mul, add_zero, inv_one, Complex.ofReal_one, one_mul]

/-- Dirichlet resolvents are dominated by the ambient resolvent in the
patch. The positive part of their difference is tested in both weak
equations. -/
theorem resolvent_le_pull (ho : IsOpen U) (hb : Bornology.IsBounded U) (s : ℝ≥0)
    (f : RealState (Fin d)) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict U,
      HeatSmallDomainDirichletHeat.resolvent s (pull a hU hm f) x ≤
        pull a hU hm (HeatTorusResolvent.step 1 s f) x := by
  by_cases hs : 0 < s
  · have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
    let g := pull a hU hm f
    let u := HeatSmallDomainDirichletResolvent.solution hs' g
    let u₀ : L2D U := (u : H1amb U) 0
    obtain ⟨V, hV, hv₀, hvform⟩ := torus_resolvent_on_patch a hU hm ho.measurableSet s hs f
    have hvpos : ∀ᵐ x ∂volume.restrict U, 0 ≤ V 0 x := by
      rw [hv₀]
      exact pull_nonnegative a hU hm _ (HeatTorusResolvent.step_nonnegative 1 s f hf)
    obtain ⟨w, hw, hwgrad⟩ := HeatH01PositivePart.exists_positive_sub ho hb u V hV hvpos
    let w₀ : L2D U := (w : H1amb U) 0
    have h0 : ⟪u₀, w₀⟫ - ⟪V 0, w₀⟫ = ‖w₀‖ ^ 2 := by
      apply inner_sub_eq_sq_of_mask
      filter_upwards [hw] with x hx
      change w₀ x = max (u₀ x - V 0 x) 0 at hx
      by_cases h : 0 ≤ u₀ x - V 0 x
      · exact Or.inl (hx.trans (max_eq_left h))
      · exact Or.inr (hx.trans (max_eq_right (le_of_not_ge h)))
    have hgrad (i : Fin d) : ⟪H01.grad u i, H01.grad w i⟫ -
        ⟪V i.succ, H01.grad w i⟫ = ‖H01.grad w i‖ ^ 2 := by
      apply inner_sub_eq_sq_of_mask
      filter_upwards [hwgrad i] with x hx
      change H01.grad w i x = (if V 0 x < u₀ x then H01.grad u i x - V i.succ x else 0) at hx
      split_ifs at hx with h
      · exact Or.inl hx
      · exact Or.inr hx
    have hd := HeatSmallDomainDirichletResolvent.variational hs' g w
    rw [HeatSmallDomainDirichletResolvent.step_apply, embL2_apply, embL2_apply, laplaceBilin_apply] at hd
    change ⟪u₀, w₀⟫ + (s : ℝ) * ∑ i : Fin d, ⟪H01.grad u i, H01.grad w i⟫ = ⟪g, w₀⟫ at hd
    have hc : ⟪V 0, w₀⟫ + (s : ℝ) * ∑ i : Fin d, ⟪V i.succ, H01.grad w i⟫ = ⟪g, w₀⟫ := hvform w
    have hsub := congrArg₂ (· - ·) hd hc
    change (⟪u₀, w₀⟫ + (s : ℝ) * ∑ i : Fin d, ⟪H01.grad u i, H01.grad w i⟫) -
      (⟪V 0, w₀⟫ + (s : ℝ) * ∑ i : Fin d, ⟪V i.succ, H01.grad w i⟫) =
        ⟪g, w₀⟫ - ⟪g, w₀⟫ at hsub
    have hE : ‖w₀‖ ^ 2 + (s : ℝ) * ∑ i : Fin d, ‖H01.grad w i‖ ^ 2 = 0 := by
      calc
        _ = (⟪u₀, w₀⟫ - ⟪V 0, w₀⟫) + (s : ℝ) *
              ∑ i : Fin d, (⟪H01.grad u i, H01.grad w i⟫ - ⟪V i.succ, H01.grad w i⟫) := by
          simp only [h0, hgrad]
        _ = 0 := by
          rw [Finset.sum_sub_distrib]
          linarith only [hsub]
    have hw0 : w₀ = 0 := by
      apply norm_eq_zero.mp
      have hn : 0 ≤ (s : ℝ) * ∑ i : Fin d, ‖H01.grad w i‖ ^ 2 :=
        mul_nonneg s.property (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      nlinarith only [hE, hn, norm_nonneg w₀]
    have hw0' := Lp.eq_zero_iff_ae_eq_zero.mp hw0
    filter_upwards [hw, hw0'] with x hx hzero
    have hpoint := le_max_left (u₀ x - V 0 x) (0 : ℝ)
    change w₀ x = _ at hx
    rw [← hx, hzero] at hpoint
    have hpoint' : u₀ x - V 0 x ≤ 0 := hpoint
    rw [HeatSmallDomainDirichletHeat.resolvent, dite_eq_left hs,
      HeatSmallDomainDirichletResolvent.step_apply, ← hv₀]
    exact sub_nonpos.mp hpoint'
  · have hs₀ : s = 0 := le_antisymm (le_of_not_gt hs) s.property
    rw [hs₀, HeatSmallDomainDirichletHeat.resolvent_zero, ContinuousLinearMap.id_apply, torus_step_zero]
    exact Eventually.of_forall fun _ => le_rfl

theorem resolvent_domination (ho : IsOpen U) (hb : Bornology.IsBounded U) (s : ℝ≥0)
    (f : RealState (Fin d)) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, push a hU hm ho.measurableSet
        (HeatSmallDomainDirichletHeat.resolvent s (pull a hU hm f)) x ≤
      HeatTorusResolvent.step 1 s f x :=
  push_le a hU hm ho.measurableSet _ _ (HeatTorusResolvent.step_nonnegative 1 s f hf)
    (resolvent_le_pull a hU hm ho hb s f hf)

end HeatTorusDirichletComparison

#print axioms HeatTorusDirichletComparison.pull_nonnegative
#print axioms HeatTorusDirichletComparison.push_le
#print axioms HeatTorusDirichletComparison.torus_resolvent_on_patch
#print axioms HeatTorusDirichletComparison.resolvent_le_pull
#print axioms HeatTorusDirichletComparison.resolvent_domination
