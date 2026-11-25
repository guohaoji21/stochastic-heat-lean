import HeatSobolevIntervalMaps
import HeatSmallIntervalSemigroup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
noncomputable section

namespace HeatSobolevAffineGraph

open EllipticPdes EllipticPdes.H1Graph Filter MeasureTheory Set
open HeatSobolevIntervalMaps HeatSmallIntervalAffine HeatSmallIntervalSemigroup
open HeatSubintervalMass HeatWeakDirichlet
open scoped ENNReal Topology RealInnerProductSpace

private def testPullback {I J : Set ℝ} (e : ℝ ≃ₜ ℝ) (hIJ : e ⁻¹' I = J)
    (he : ContDiff ℝ (⊤ : ℕ∞) (e : ℝ → ℝ)) (c : ℝ) (φ : testFunctions I) : testFunctions J := by
  let ψ : ℝ → ℝ := c • ((φ : ℝ → ℝ) ∘ e)
  have hs : tsupport ψ ⊆ e ⁻¹' tsupport (φ : ℝ → ℝ) := by
    rw [← tsupport_comp_eq_preimage _ e]
    exact tsupport_smul_subset_right (fun _ : ℝ => c) ((φ : ℝ → ℝ) ∘ e)
  exact ⟨ψ, contDiff_const.mul (φ.2.1.comp he),
    (e.isCompact_preimage.mpr φ.2.2.1).of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (hIJ ▸ preimage_mono φ.2.2.2)⟩

private theorem map_testGraph {I J : Set ℝ} (e : ℝ ≃ₜ ℝ) (hIJ : e ⁻¹' I = J)
    (he : ContDiff ℝ (⊤ : ℕ∞) (e : ℝ → ℝ)) {k : ℝ} (hder : ∀ x, HasDerivAt (e : ℝ → ℝ) k x)
    (hmp : QuasiMeasurePreserving e (volume.restrict J) (volume.restrict I))
    (q : State I →L[ℝ] State J) (c : ℝ)
    (hq : ∀ f : State I, (q f : ℝ → ℝ) =ᵐ[volume.restrict J] fun x => c * f (e x))
    (φ : testFunctions I) : mapGraph q (k • q) (testGraphₗ volume I φ) =
      testGraphₗ volume J (testPullback e hIJ he c φ) := by
  let U := testGraphₗ (volume : Measure ℝ) I φ
  let ψ := testPullback e hIJ he c φ
  apply H1Graph.ext
  · simp only [fnL_mapGraph]
    apply Lp.ext
    filter_upwards [hq (fnL U), hmp.ae (coeFn_fnL_testGraphₗ φ), coeFn_fnL_testGraphₗ ψ]
      with x hqf hφ hψ
    exact hqf.trans ((congrArg (c * ·) hφ).trans hψ.symm)
  · simp only [gradL_mapGraph, smul_apply]
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul k (q (gradL U)), hq (gradL U),
      hmp.ae (coeFn_gradL_testGraphₗ φ), coeFn_gradL_testGraphₗ ψ] with x hk hqg hφ hψ
    have hφd := ((φ.2.1.differentiable (by simp) (e x)).hasDerivAt.comp x (hder x)).const_mul c
    have hψd : gradient (ψ : ℝ → ℝ) x = c * (deriv (φ : ℝ → ℝ) (e x) * k) :=
      gradient_eq_deriv'.trans hφd.deriv
    change (k • q (gradL U)) x = gradL (testGraphₗ volume J ψ) x
    rw [hk, Pi.smul_apply, smul_eq_mul, hqg, hφ, hψ, hψd, gradient_eq_deriv']
    ring

private theorem mapGraph_mem_H01 {I J : Set ℝ} (e : ℝ ≃ₜ ℝ) (hIJ : e ⁻¹' I = J)
    (he : ContDiff ℝ (⊤ : ℕ∞) (e : ℝ → ℝ)) {k : ℝ} (hder : ∀ x, HasDerivAt (e : ℝ → ℝ) k x)
    (hmp : QuasiMeasurePreserving e (volume.restrict J) (volume.restrict I))
    (q : State I →L[ℝ] State J) (c : ℝ)
    (hq : ∀ f : State I, (q f : ℝ → ℝ) =ᵐ[volume.restrict J] fun x => c * f (e x))
    {U : Graph I} (hU : U ∈ H01 volume I) : mapGraph q (k • q) U ∈ H01 volume J := by
  obtain ⟨φ, hφ⟩ := exists_seq_testGraphₗ_tendsto hU
  refine isClosed_H01.mem_of_tendsto ((mapGraph q (k • q)).continuous.continuousAt.tendsto.comp hφ)
    (Eventually.of_forall fun n => ?_)
  rw [Function.comp_apply, map_testGraph e hIJ he hder hmp q c hq]
  exact testGraphₗ_mem_H01 _

theorem plateau_subset_domain : plateau ⊆ domain := by
  intro x hx
  have h : x ∈ Ioo (25 / 4 : ℝ) (27 / 4 : ℝ) := hx
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private def coord : ℝ ≃ₜ ℝ :=
  (Homeomorph.addRight (-(25 / 4 : ℝ))).trans (Homeomorph.mulLeft₀ 20 (by norm_num))

private theorem coord_apply (x : ℝ) : coord x = toLarge x := rfl

private theorem coord_symm_apply (x : ℝ) : coord.symm x = x / 20 + 25 / 4 := by
  have h := coord.apply_symm_apply x
  rw [coord_apply, toLarge_apply] at h
  linarith

private theorem preimage_coord : coord ⁻¹' domain = plateau := preimage_large

private theorem preimage_coord_symm : coord.symm ⁻¹' plateau = domain := by
  rw [← preimage_coord]
  ext x
  simp

private theorem coord_mp : MeasurePreserving toLarge (volume.restrict plateau)
    (ENNReal.ofReal (1 / 20 : ℝ) • volume.restrict domain) := by
  refine ⟨toLarge.measurable, ?_⟩
  rw [← nestedMeasure plateau_subset_domain]
  exact map_subinterval

private theorem coord_qmp : QuasiMeasurePreserving coord (volume.restrict plateau)
    (volume.restrict domain) :=
  coord_mp.quasiMeasurePreserving.mono_right Measure.smul_absolutelyContinuous

private theorem coord_symm_qmp : QuasiMeasurePreserving coord.symm (volume.restrict domain)
    (volume.restrict plateau) :=
  (coord_mp.symm toLarge).quasiMeasurePreserving.mono_left
    (Measure.absolutelyContinuous_smul (by norm_num : ENNReal.ofReal (1 / 20 : ℝ) ≠ 0))

private theorem plateauMeasure_eq : smallMeasure = volume.restrict plateau :=
  nestedMeasure plateau_subset_domain

private theorem plateauMeasure_le : (volume : Measure ℝ).restrict plateau ≤ (1 : ℝ≥0∞) • smallMeasure := by
  rw [one_smul]
  exact plateauMeasure_eq.ge

private def normalizeLinear : SubintervalState →L[ℝ] State plateau :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top plateauMeasure_le

private theorem normalizeLinear_ae (f : SubintervalState) :
    (normalizeLinear f : ℝ → ℝ) =ᵐ[volume.restrict plateau] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top plateauMeasure_le f

private def normalizeIsometry : SubintervalState →ₗᵢ[ℝ] State plateau where
  toLinearMap := normalizeLinear.toLinearMap
  norm_map' f := by
    change ‖normalizeLinear f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (normalizeLinear_ae f), ← plateauMeasure_eq]

/-- Reinterpret an `L²` class using the restriction of volume to the plateau. -/
def normalizePlateau : SubintervalState ≃ₗᵢ[ℝ] State plateau :=
  LinearIsometryEquiv.ofSurjective normalizeIsometry (by
    intro f
    have hf := (Lp.memLp f).mono_measure (le_of_eq plateauMeasure_eq)
    refine ⟨hf.toLp f, Lp.ext ?_⟩
    change (normalizeLinear (hf.toLp f) : ℝ → ℝ) =ᵐ[volume.restrict plateau] f
    exact (normalizeLinear_ae _).trans (hf.coeFn_toLp.filter_mono (ae_mono plateauMeasure_eq.ge)))

theorem normalizePlateau_ae (f : SubintervalState) :
    (normalizePlateau f : ℝ → ℝ) =ᵐ[volume.restrict plateau] f :=
  normalizeLinear_ae f

/-- Affine transport with the plateau measure expressed as a single restriction. -/
def transportL2 : HeatIntervalNormalization.Base ≃ₗᵢ[ℝ] State plateau :=
  transport.trans normalizePlateau

theorem transportL2_apply (f : HeatIntervalNormalization.Base) :
    transportL2 f = normalizePlateau (transport f) := by
  simp only [transportL2, LinearIsometryEquiv.trans_apply]

private theorem transportL2_ae (f : HeatIntervalNormalization.Base) : (transportL2 f : ℝ → ℝ) =ᵐ[volume.restrict plateau]
    fun x => Real.sqrt 20 * f (coord x) := by
  rw [transportL2_apply]
  have h := normalizePlateau_ae (transport f)
  refine h.trans ?_
  exact (transport_ae f).filter_mono (ae_mono (le_of_eq (nestedMeasure plateau_subset_domain).symm))

private theorem transportL2_symm_ae (f : State plateau) :
    (transportL2.symm f : ℝ → ℝ) =ᵐ[volume.restrict domain]
      fun x => (Real.sqrt 20)⁻¹ * f (coord.symm x) := by
  have h := transportL2_ae (transportL2.symm f)
  rw [transportL2.apply_symm_apply] at h
  filter_upwards [coord_symm_qmp.ae h] with x hx
  change f (coord.symm x) = Real.sqrt 20 * transportL2.symm f (coord (coord.symm x)) at hx
  rw [coord.apply_symm_apply] at hx
  rw [hx, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)), one_mul]

def toPlateau : Graph domain →L[ℝ] Graph plateau :=
  mapGraph transportL2.toLinearIsometry.toContinuousLinearMap
    ((20 : ℝ) • transportL2.toLinearIsometry.toContinuousLinearMap)

def fromPlateau : Graph plateau →L[ℝ] Graph domain :=
  mapGraph transportL2.symm.toLinearIsometry.toContinuousLinearMap
    ((1 / 20 : ℝ) • transportL2.symm.toLinearIsometry.toContinuousLinearMap)

@[simp] theorem fnL_toPlateau (U : Graph domain) : fnL (toPlateau U) = transportL2 (fnL U) := rfl

@[simp] theorem gradL_toPlateau (U : Graph domain) :
    gradL (toPlateau U) = (20 : ℝ) • transportL2 (gradL U) := rfl

@[simp] theorem fnL_fromPlateau (U : Graph plateau) :
    fnL (fromPlateau U) = transportL2.symm (fnL U) := rfl

@[simp] theorem gradL_fromPlateau (U : Graph plateau) :
    gradL (fromPlateau U) = (1 / 20 : ℝ) • transportL2.symm (gradL U) := rfl

theorem toPlateau_mem_H01 {U : Graph domain} (hU : U ∈ H01 volume domain) :
    toPlateau U ∈ H01 volume plateau := by
  unfold toPlateau
  refine mapGraph_mem_H01 coord preimage_coord ?_ ?_ coord_qmp
    transportL2.toLinearIsometry.toContinuousLinearMap (Real.sqrt 20) (fun f => transportL2_ae f) hU
  · have h : (coord : ℝ → ℝ) = fun x => 20 * (x - 25 / 4) := funext toLarge_apply
    rw [h]
    fun_prop
  · intro x
    have h : (coord : ℝ → ℝ) = fun x => 20 * (x - 25 / 4) := funext toLarge_apply
    rw [h]
    simpa using ((hasDerivAt_id x).sub_const (25 / 4)).const_mul 20

theorem fromPlateau_mem_H01 {U : Graph plateau} (hU : U ∈ H01 volume plateau) :
    fromPlateau U ∈ H01 volume domain := by
  unfold fromPlateau
  refine mapGraph_mem_H01 coord.symm preimage_coord_symm ?_ ?_ coord_symm_qmp
    transportL2.symm.toLinearIsometry.toContinuousLinearMap (Real.sqrt 20)⁻¹
    (fun f => transportL2_symm_ae f) hU
  · rw [funext coord_symm_apply]
    fun_prop
  · intro x
    rw [funext coord_symm_apply]
    simpa using ((hasDerivAt_id x).div_const 20).add_const (25 / 4)

theorem toPlateau_fromPlateau (U : Graph plateau) : toPlateau (fromPlateau U) = U := by
  apply H1Graph.ext
  · calc
      _ = transportL2 (fnL (fromPlateau U)) := fnL_toPlateau _
      _ = transportL2 (transportL2.symm (fnL U)) := congrArg
        (fun f : HeatIntervalNormalization.Base => transportL2 f) (fnL_fromPlateau U)
      _ = _ := transportL2.apply_symm_apply _
  · calc
      _ = (20 : ℝ) • transportL2 (gradL (fromPlateau U)) := gradL_toPlateau _
      _ = (20 : ℝ) • transportL2 ((1 / 20 : ℝ) • transportL2.symm (gradL U)) := congrArg
        (fun f : HeatIntervalNormalization.Base => (20 : ℝ) • transportL2 f) (gradL_fromPlateau U)
      _ = _ := by
        rw [map_smul, transportL2.apply_symm_apply, smul_smul]
        norm_num

theorem inner_grad_toPlateau (U V : Graph domain) :
    inner ℝ (gradL (toPlateau U)) (gradL (toPlateau V)) = 400 * inner ℝ (gradL U) (gradL V) := by
  rw [gradL_toPlateau, gradL_toPlateau, real_inner_smul_left, real_inner_smul_right,
    transportL2.inner_map_map]
  ring <;> rfl

end HeatSobolevAffineGraph

#print axioms HeatSobolevAffineGraph.toPlateau_mem_H01
#print axioms HeatSobolevAffineGraph.fromPlateau_mem_H01
#print axioms HeatSobolevAffineGraph.toPlateau_fromPlateau
#print axioms HeatSobolevAffineGraph.inner_grad_toPlateau
