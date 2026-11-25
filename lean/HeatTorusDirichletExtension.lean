import HeatTorusPatchSobolev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
set_option synthInstance.maxHeartbeats 150000
noncomputable section

namespace HeatTorusDirichletExtension

open Filter MeasureTheory Set UnitAddTorus EllipticPdes.Sobolev
open HeatTorusFourier HeatTorusReal HeatTorusGradient HeatTorusPatchSobolev
open HeatFlatTorusSmoothLift (covering)
open HeatTorusFundamentalCell (cell patchEquiv patch_measurePreserving)
open HeatTorusFourierLift (phase phase_single hasFDerivAt_character)
open HeatRestrictionAdjoint (restriction restriction_ae adjointExtension adjointExtension_ae)
open scoped Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
variable (a : Fin d → ℝ) (hU : U ⊆ cell a)
  (hm : MeasurableSet (covering 1 '' U)) (hUm : MeasurableSet U)

theorem pull_push (g : L2D U) : pull a hU hm (push a hU hm hUm g) = g := by
  let S := covering 1 '' U
  let e := patchEquiv a hU hUm hm
  let f := e.symm g
  have h : restriction volume S (adjointExtension volume S f) = f := by
    apply Lp.ext
    filter_upwards [restriction_ae volume S (adjointExtension volume S f),
      ae_restrict_of_ae (adjointExtension_ae volume S hm f), ae_restrict_mem hm] with x h₁ h₂ h₃
    rw [h₁, h₂, indicator_of_mem h₃]
  change e (restriction volume S (adjointExtension volume S f)) = g
  rw [h]
  exact e.apply_symm_apply g

private theorem push_coefficient (g : L2D U) (k : Fin d → ℤ) :
    mFourierCoeff (embed (push a hU hm hUm g)) k =
      ∫ x in U, mFourier (-k) (covering 1 x) * (g x : ℂ) := by
  let S := covering 1 '' U
  let p := push a hU hm hUm g
  let F (x : UnitAddTorus (Fin d)) := mFourier (-k) x * (p x : ℂ)
  let hc := patch_measurePreserving a hU hm
  have hF : AEStronglyMeasurable F (volume.restrict S) :=
    (mFourier (-k)).continuous.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable p).mono_measure Measure.restrict_le_self))
  calc
    _ = ∫ x, F x := by
      apply integral_congr_ae
      filter_upwards [embed_ae p] with x hx
      change mFourier (-k) x * embed p x = F x
      rw [hx]
    _ = ∫ x in S, F x := by
      rw [← integral_indicator hm]
      apply integral_congr_ae
      filter_upwards [push_ae a hU hm hUm g] with x hx
      by_cases hs : x ∈ S
      · rw [indicator_of_mem hs]
      · rw [indicator_of_notMem hs]
        change mFourier (-k) x * (p x : ℂ) = 0
        rw [show p x = 0 from hx.trans (indicator_of_notMem hs _), Complex.ofReal_zero, mul_zero]
    _ = ∫ x in U, F (covering 1 x) := by
      rw [← hc.map_eq] at hF ⊢
      exact integral_map hc.aemeasurable hF
    _ = _ := by
      apply integral_congr_ae
      have hp := (pull_ae a hU hm p).symm
      rw [show pull a hU hm p = g from pull_push a hU hm hUm g] at hp
      filter_upwards [hp] with x hx
      change mFourier (-k) (covering 1 x) * (p (covering 1 x) : ℂ) = _
      rw [show p (covering 1 x) = g x from hx]

private theorem test_gradient {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsTestFn U φ) :
    HasGradient 1 (embed (push a hU hm hUm hφ.testCls))
      (fun i => embed (push a hU hm hUm (hφ.partialCls i))) := by
  intro i k
  rw [push_coefficient, push_coefficient]
  let C (x : EuclideanSpace ℝ (Fin d)) := mFourier (-k) (covering 1 x)
  let G (x : EuclideanSpace ℝ (Fin d)) := (φ x : ℂ)
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  have hc (x : EuclideanSpace ℝ (Fin d)) :
      HasFDerivAt C (C x • phase (-k)) x := hasFDerivAt_character (-k) x
  have hd (x : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ C x e = C x * symbol 1 i (-k) := by
    rw [(hc x).fderiv, smul_apply, phase_single, smul_eq_mul]
  have hGder (x : EuclideanSpace ℝ (Fin d)) :
      HasFDerivAt G (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x ((hφ.1.differentiable (by simp)) x).hasFDerivAt
  have hg (x : EuclideanSpace ℝ (Fin d)) : fderiv ℝ G x e = (partialD i φ x : ℂ) := by
    rw [(hGder x).fderiv]
    rfl
  have hC : Continuous C := continuous_iff_continuousAt.mpr fun x => (hc x).continuousAt
  have hG : Continuous G := Complex.continuous_ofReal.comp hφ.continuous
  have hφc : HasCompactSupport G := hφ.2.1.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hpartial : HasCompactSupport (fun x => (partialD i φ x : ℂ)) :=
    (hφ.hasCompactSupport_partialD i).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have h₁ : Integrable (fun x => fderiv ℝ C x e * G x) volume := by
    simp_rw [hd]
    exact ((hC.mul continuous_const).mul hG).integrable_of_hasCompactSupport hφc.mul_left
  have h₂ : Integrable (fun x => C x * fderiv ℝ G x e) volume := by
    simp_rw [hg]
    apply Continuous.integrable_of_hasCompactSupport
      (hC.mul (Complex.continuous_ofReal.comp (hφ.continuous_partialD i)))
    exact hpartial.mul_left
  have h₃ : Integrable (fun x => C x * G x) volume :=
    (hC.mul hG).integrable_of_hasCompactSupport hφc.mul_left
  have hlim := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
    (fun x _ => (hc x).differentiableAt) (fun x _ => (hGder x).differentiableAt)
  simp_rw [hd, hg] at hlim
  have hs : symbol 1 i (-k) = -symbol 1 i k := by
    simp [symbol, Pi.neg_apply]
  rw [hs] at hlim
  have hrew (x : EuclideanSpace ℝ (Fin d)) : C x * -symbol 1 i k * G x =
      (-symbol 1 i k) * (C x * G x) := by ring
  simp_rw [hrew, integral_const_mul, neg_mul, neg_neg] at hlim
  convert hlim using 1
  · calc
      _ = ∫ x in U, C x * (partialD i φ x : ℂ) := by
        apply integral_congr_ae
        filter_upwards [(hφ.memLp_partialD i).coeFn_toLp] with x hx
        rw [show hφ.partialCls i x = _ from hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun h => hx (hφ.2.2 (tsupport_partialD_subset i φ h))), Complex.ofReal_zero, mul_zero])
  · congr 1
    calc
      _ = ∫ x in U, C x * G x := by
        apply integral_congr_ae
        filter_upwards [hφ.memLp.coeFn_toLp] with x hx
        rw [show hφ.testCls x = φ x from hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        change C x * (φ x : ℂ) = 0
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), Complex.ofReal_zero, mul_zero])

/-- The zero extension of a Dirichlet Sobolev graph has the same Fourier
gradient as the zero extensions of its Euclidean weak partial derivatives. -/
theorem push_gradient (v : H01 U) :
    HasGradient 1 (embed (push a hU hm hUm ((v : H1amb U) 0)))
      (fun i => embed (push a hU hm hUm (H01.grad v i))) := by
  intro i k
  let L := embed.comp (push a hU hm hUm)
  let M := (HeatTorusFourier.coefficientCLM k).comp L
  have hM (g : L2D U) : M g = mFourierCoeff (embed (push a hU hm hUm g)) k :=
    HeatTorusFourier.coefficientCLM_apply k _
  have hc (j : Fin (d + 1)) : Continuous (fun X : H1amb U => M (X j)) :=
    M.continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => L2D U) j)
  let S := { X : H1amb U | M (X i.succ) = symbol 1 i k * M (X 0) }
  have hS : IsClosed S := isClosed_eq (hc i.succ) (continuous_const.mul (hc 0))
  have hs : testGraphSet U ⊆ S := by
    rintro _ ⟨φ, hφ, rfl⟩
    change M (hφ.testGraph i.succ) = symbol 1 i k * M (hφ.testGraph 0)
    rw [IsTestFn.testGraph_zero, IsTestFn.testGraph_succ, hM, hM]
    exact test_gradient a hU hm hUm hφ i k
  have hv : (v : H1amb U) ∈ closure (testGraphSet U) := by
    rw [← coe_H01]
    exact v.2
  have he := closure_minimal hs hS hv
  change M ((v : H1amb U) i.succ) = symbol 1 i k * M ((v : H1amb U) 0) at he
  rw [hM, hM] at he
  exact he

end HeatTorusDirichletExtension

#print axioms HeatTorusDirichletExtension.pull_push
#print axioms HeatTorusDirichletExtension.push_gradient
