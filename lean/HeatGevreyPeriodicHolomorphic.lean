import HeatGevreyAxisBridge
import HeatGevreyFourierExtension
import HeatTorusInitialData
import Mathlib.Analysis.Calculus.Deriv.CompMul

set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section

namespace HeatGevreyPeriodicHolomorphic

open Set HeatGevreyProduct HeatGevreyFourierExtension
open HeatTorusGevreyCutoff (chart)
open HeatTorusGaussian (wrap)
open HeatTorusInitialData (rescale rescale_coe)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem coordinateDeriv_dilate (i : ι) (P A : ℝ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    coordinateDeriv i (fun v => A * f (P • v)) x = A * P * coordinateDeriv i f (P • x) := by
  have he (t : ℝ) : P • Function.update x i t = Function.update (P • x) i (P * t) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [smul_eq_mul]
    · simp [Function.update_of_ne hj]
  unfold coordinateDeriv
  simp_rw [he]
  rw [deriv_const_mul_field, deriv_comp_mul_left P (fun t => f (Function.update (P • x) i t))]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem mixedPartial_dilate (l : List ι) (P : ℝ) (f : (ι → ℝ) → ℝ) :
    mixedPartial l (f ∘ fun x => P • x) = fun x => P ^ l.length * mixedPartial l f (P • x) := by
  induction l with
  | nil => simp [mixedPartial, Function.comp_def]
  | cons i l ih =>
    funext x
    rw [mixedPartial, ih, coordinateDeriv_dilate, mixedPartial, List.length_cons, pow_succ]

private theorem rescale_wrap {P : ℝ} (hP : 0 < P) (x : ι → ℝ) :
    rescale hP (wrap x) = chart (0 : ι → AddCircle P) (P • x) := by
  funext i
  change rescale hP (fun j => (x j : UnitAddCircle)) i = _
  rw [rescale_coe]
  simp [chart, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- The physical-period Gevrey-1 assumption gives exponential decay of the
Fourier coefficients after unit-period normalization. -/
theorem exists_coefficient_decay [Nonempty ι] {P : ℝ} (hP : 0 < P)
    (b : (ι → AddCircle P) → ℝ) (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b ∘ chart 0))
    (hD : ∀ (l : List ι) x, |mixedPartial l (b ∘ chart 0) x| ≤
      C * ρ ^ l.length * (l.length.factorial : ℝ)) :
    ∃ g : C(UnitAddTorus ι, ℂ), (∀ x, g x = (b (rescale hP x) : ℂ)) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ k : ι → ℤ,
        ‖UnitAddTorus.mFourierCoeff g k‖ ≤ 2 * C * Real.exp (-a * weight k) := by
  let b₀ : UnitAddTorus ι → ℝ := b ∘ rescale hP
  have he : b₀ ∘ wrap = (b ∘ chart 0) ∘ (fun x : ι → ℝ => P • x) := by
    funext x
    exact congrArg b (rescale_wrap hP x)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (b₀ ∘ wrap) := by
    rw [he]
    exact hb.comp (contDiff_id.const_smul P)
  let g : C(UnitAddTorus ι, ℂ) := ⟨fun x => (b₀ x : ℂ), Complex.continuous_ofReal.comp
    (HeatGevreyAxisBridge.wrap_isQuotientMap.continuous_iff.mpr hs.continuous)⟩
  refine ⟨g, fun _ => rfl, HeatGevreyAxisBridge.coefficient_decay b₀ C (P * ρ) hC (mul_pos hP hρ) hs ?_⟩
  intro l x
  rw [he, mixedPartial_dilate, abs_mul, abs_of_nonneg (pow_nonneg hP.le _), mul_pow]
  convert mul_le_mul_of_nonneg_left (hD l (P • x)) (pow_nonneg hP.le l.length) using 1
  ring

/-- The Gevrey-1 bound on the physical torus implies a bounded periodic
holomorphic extension to a complex tube of positive width. -/
theorem exists_periodic_holomorphic_extension [Nonempty ι] {P : ℝ} (hP : 0 < P)
    (b : (ι → AddCircle P) → ℝ) (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b ∘ chart 0))
    (hD : ∀ (l : List ι) x, |mixedPartial l (b ∘ chart 0) x| ≤
      C * ρ ^ l.length * (l.length.factorial : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : (ι → ℂ) → ℂ, DifferentiableOn ℂ F (tube r) ∧
      (∀ x : ι → ℝ, F (fun i => (x i : ℂ)) = (b (chart 0 x) : ℂ)) ∧
      (∀ (z : ι → ℂ) (v : ι → ℤ), F (z + fun i => (P : ℂ) * (v i : ℂ)) = F z) ∧
      ∃ B : ℝ, ∀ z ∈ tube r, ‖F z‖ ≤ B := by
  obtain ⟨g, hg, a, ha, hdec⟩ := exists_coefficient_decay hP b C ρ hC hρ hb hD
  obtain ⟨r, hr, F, hF, hreal, hperiod, B, hbound⟩ := exists_extension g (2 * C) a (by positivity) ha hdec
  let A : (ι → ℂ) →L[ℂ] (ι → ℂ) := (P⁻¹ : ℝ) • ContinuousLinearMap.id ℂ (ι → ℂ)
  have hA (z : ι → ℂ) (i : ι) : (A z) i = (P⁻¹ : ℝ) * z i := rfl
  have hm : MapsTo A (tube (P * r)) (tube r) := by
    intro z hz
    apply mem_iInter.mpr
    intro i
    have hi : |(z i).im| < P * r := abs_lt.mpr (mem_iInter.mp hz i)
    apply abs_lt.mp
    change |(A z i).im| < r
    simp only [hA, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_pos (inv_pos.mpr hP)]
    exact (inv_mul_lt_iff₀ hP).mpr hi
  refine ⟨P * r, mul_pos hP hr, F ∘ A, hF.comp A.differentiable.differentiableOn hm, ?_, ?_, B, ?_⟩
  · intro x
    have hx : A (fun i => (x i : ℂ)) = fun i => ((P⁻¹ * x i : ℝ) : ℂ) := by
      funext i
      rw [hA, Complex.ofReal_mul]
    change F (A (fun i => (x i : ℂ))) = _
    rw [hx, hreal, hg]
    change (b (rescale hP (wrap (P⁻¹ • x))) : ℂ) = _
    rw [rescale_wrap hP, smul_smul, mul_inv_cancel₀ hP.ne', one_smul]
  · intro z v
    have hv : A (fun i => (P : ℂ) * (v i : ℂ)) = fun i => (v i : ℂ) := by
      funext i
      rw [hA, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hP.ne', Complex.ofReal_one, one_mul]
    change F (A (z + fun i => (P : ℂ) * (v i : ℂ))) = F (A z)
    rw [map_add, hv, hperiod]
  · exact fun z hz => hbound _ (hm hz)

end HeatGevreyPeriodicHolomorphic

#print axioms HeatGevreyPeriodicHolomorphic.exists_coefficient_decay
#print axioms HeatGevreyPeriodicHolomorphic.exists_periodic_holomorphic_extension
