import HeatTorusFundamentalCell
import HeatTorusFourierLift
import HeatRestrictionAdjoint
import EllipticPdes.Sobolev.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 150000
noncomputable section

namespace HeatTorusPatchSobolev

open MeasureTheory Set Filter UnitAddTorus HeatTorusFourier HeatTorusReal HeatTorusGradient
open HeatFlatTorusSmoothLift (covering)
open HeatTorusFundamentalCell (cell patch_measurePreserving patchPullback patchEquiv)
open HeatTorusFourierLift (profile profileDerivative hasFDerivAt_profile profileDerivative_single)
open HeatRestrictionAdjoint (restriction restriction_ae adjointExtension adjointExtension_ae
  restriction_adjoint_pairing)
open HeatTorusGalerkinProjection (analysis project project_tendsto)
open HeatTorusGalerkinCompression (synthesis_ae)
open EllipticPdes.Sobolev
open scoped Topology RealInnerProductSpace

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
variable (a : Fin d → ℝ) (hU : U ⊆ cell a) (hm : MeasurableSet (covering 1 '' U))

/-- Restriction to a torus patch, followed by pullback to its Euclidean coordinates. -/
def pull : RealState (Fin d) →L[ℝ] L2D U :=
  (patchPullback a hU hm).toContinuousLinearMap.comp (restriction volume (covering 1 '' U))

theorem pull_ae (f : RealState (Fin d)) :
    (pull a hU hm f : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict U] f ∘ covering 1 := by
  let hc := patch_measurePreserving a hU hm
  let f' := restriction volume (covering 1 '' U) f
  exact (Lp.coeFn_compMeasurePreserving f' hc).trans
    (hc.quasiMeasurePreserving.ae (restriction_ae volume (covering 1 '' U) f))

/-- Transport a Euclidean patch function to the torus and extend by zero. -/
def push (hUm : MeasurableSet U) : L2D U →L[ℝ] RealState (Fin d) :=
  (adjointExtension volume (covering 1 '' U)).comp
    (patchEquiv a hU hUm hm).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem push_ae (hUm : MeasurableSet U) (g : L2D U) :
    (push a hU hm hUm g : UnitAddTorus (Fin d) → ℝ) =ᵐ[volume]
      (covering 1 '' U).indicator ((patchEquiv a hU hUm hm).symm g) :=
  adjointExtension_ae volume (covering 1 '' U) hm _

theorem pull_push_pairing (hUm : MeasurableSet U) (f : RealState (Fin d)) (g : L2D U) :
    ⟪pull a hU hm f, g⟫ = ⟪f, push a hU hm hUm g⟫ := by
  let e := patchEquiv a hU hUm hm
  change ⟪e (restriction volume (covering 1 '' U) f), g⟫ =
    ⟪f, adjointExtension volume (covering 1 '' U) (e.symm g)⟫
  rw [← restriction_adjoint_pairing, ← e.inner_map_map, e.apply_symm_apply]

def graph (f : State (Fin d)) (D : Fin d → State (Fin d)) : H1amb U :=
  WithLp.toLp 2 (Fin.cons (pull a hU hm (realPart f)) (fun i => pull a hU hm (realPart (D i))))

private theorem profile_ae (S : Finset (Fin d → ℤ)) (f : State (Fin d)) :
    (pull a hU hm (realPart (project S f)) : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict U]
      fun x => (profile S f x).re := by
  let hc := patch_measurePreserving a hU hm
  have hproj := (synthesis_ae S (analysis S f)).fun_comp Complex.re
  have hrep := (realPart_ae (project S f)).trans hproj
  filter_upwards [pull_ae a hU hm (realPart (project S f)),
    hc.quasiMeasurePreserving.ae (ae_restrict_of_ae hrep)] with x hx hy
  exact hx.trans hy

private theorem finite_mem (S : Finset (Fin d → ℤ)) (f : State (Fin d))
    (D : Fin d → State (Fin d)) (hD : HasGradient 1 f D) :
    graph a hU hm (project S f) (fun i => project S (D i)) ∈ W12 U := by
  rw [mem_W12_iff]
  intro φ hφ i
  change ⟪hφ.partialCls i, pull a hU hm (realPart (project S f))⟫ +
    ⟪hφ.testCls, pull a hU hm (realPart (project S (D i)))⟫ = 0
  let u (x : EuclideanSpace ℝ (Fin d)) := (profile S f x).re
  let g (x : EuclideanSpace ℝ (Fin d)) := (profile S (D i) x).re
  have hd (x : EuclideanSpace ℝ (Fin d)) :
      HasFDerivAt u (Complex.reCLM.comp (profileDerivative S f x)) x :=
    Complex.reCLM.hasFDerivAt.comp x (hasFDerivAt_profile S f x)
  have hg : partialD i u = g := by
    funext x
    rw [partialD_apply, (hd x).fderiv]
    change (profileDerivative S f x (EuclideanSpace.single i 1)).re = _
    rw [profileDerivative_single S f D hD]
  have hu : Continuous u := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x =>
    (Complex.reCLM.hasFDerivAt.comp x (hasFDerivAt_profile S (D i) x)).continuousAt
  have h₁ : ⟪hφ.partialCls i, pull a hU hm (realPart (project S f))⟫ =
      ∫ x, partialD i φ x * u x := by
    rw [L2.real_inner_eq_integral]
    calc
      _ = ∫ x in U, partialD i φ x * u x := by
        apply integral_congr_ae
        filter_upwards [(hφ.memLp_partialD i).coeFn_toLp, profile_ae a hU hm S f] with x hx hy
        rw [show hφ.partialCls i x = partialD i φ x from hx, hy]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun h => hx (hφ.2.2 (tsupport_partialD_subset i φ h))), zero_mul])
  have h₂ : ⟪hφ.testCls, pull a hU hm (realPart (project S (D i)))⟫ =
      ∫ x, φ x * g x := by
    rw [L2.real_inner_eq_integral]
    calc
      _ = ∫ x in U, φ x * g x := by
        apply integral_congr_ae
        filter_upwards [hφ.memLp.coeFn_toLp, profile_ae a hU hm S (D i)] with x hx hy
        rw [show hφ.testCls x = φ x from hx, hy]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), zero_mul])
  rw [h₁, h₂, ← hg]
  simp only [partialD]
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := φ) (g := u)
    (((hφ.continuous_partialD i).mul hu).integrable_of_hasCompactSupport
      (hφ.hasCompactSupport_partialD i).mul_right)
    ((hφ.continuous.mul hgc).integrable_of_hasCompactSupport hφ.2.1.mul_right |>.congr
      (Eventually.of_forall fun x => congrArg (φ x * ·) (congrFun hg x).symm))
    ((hφ.continuous.mul hu).integrable_of_hasCompactSupport hφ.2.1.mul_right)
    (fun x _ => (hφ.1.differentiable (by simp)).differentiableAt)
    (fun x _ => (hd x).differentiableAt)]
  rw [add_neg_cancel]

/-- The pullback of an (L²) Fourier gradient gives the weak Euclidean
Sobolev gradient on every measurable patch inside a cell. -/
theorem graph_mem_W12 (f : State (Fin d)) (D : Fin d → State (Fin d)) (hD : HasGradient 1 f D) :
    graph a hU hm f D ∈ W12 U := by
  apply (Submodule.span ℝ (constraintSet U)).isClosed_orthogonal.mem_of_tendsto
    (b := atTop) (f := fun S : Finset (Fin d → ℤ) =>
      graph a hU hm (project S f) (fun i => project S (D i))) _ (Eventually.of_forall
        fun S => finite_mem a hU hm S f D hD)
  let L := (pull a hU hm).comp (realPart (ι := Fin d))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => L2D U)).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro j
  induction j using Fin.cases with
  | zero =>
    exact (L.continuous.continuousAt.tendsto.comp (project_tendsto f))
  | succ i =>
    exact (L.continuous.continuousAt.tendsto.comp (project_tendsto (D i)))

end HeatTorusPatchSobolev

#print axioms HeatTorusPatchSobolev.pull_ae
#print axioms HeatTorusPatchSobolev.push_ae
#print axioms HeatTorusPatchSobolev.pull_push_pairing
#print axioms HeatTorusPatchSobolev.graph_mem_W12
