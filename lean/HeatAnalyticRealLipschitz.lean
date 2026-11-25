import HeatAnalyticPeriodicPropagation
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section

namespace HeatAnalyticRealLipschitz

open Metric Set HeatAnalyticStripPropagation HeatAnalyticPeriodicPropagation HeatGevreyFourierExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_sub_on_real_line {f : ℂ → E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (strip ρ)) (hcap : ∀ z ∈ strip ρ, ‖f z‖ ≤ M) (s t : ℝ) :
    ‖f t - f s‖ ≤ (M / (ρ / 2)) * ‖t - s‖ := by
  let g : ℝ → E := fun x => f x
  have hclosed (x : ℝ) : closedBall (x : ℂ) (ρ / 2) ⊆ strip ρ := by
    intro z hz
    have hn : ‖z - (x : ℂ)‖ ≤ ρ / 2 := by simpa only [dist_eq_norm] using mem_closedBall.mp hz
    have him := (Complex.abs_im_le_norm (z - x)).trans hn
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    exact him.trans_lt (by linarith)
  have hopen : IsOpen (strip ρ) := isOpen_lt (Complex.continuous_im.abs) continuous_const
  have hg (x : ℝ) : HasDerivAt g (deriv f (x : ℂ)) x := by
    have hx : (x : ℂ) ∈ strip ρ := by simpa [strip] using hρ
    have hd := ((hf x hx).differentiableAt (hopen.mem_nhds hx)).hasDerivAt
    have h := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x Complex.ofRealCLM.hasDerivAt
    change HasDerivAt g ((1 : ℂ) • deriv f (x : ℂ)) x at h
    simpa only [one_smul] using h
  have hbound (x : ℝ) : ‖deriv g x‖ ≤ M / (ρ / 2) := by
    rw [(hg x).deriv]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      ((hf.mono ((closure_ball_subset_closedBall).trans (hclosed x))).diffContOnCl)
      (fun z hz => hcap z (hclosed x (sphere_subset_closedBall hz)))
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => (hg x).differentiableAt)
    (fun x _ => hbound x) convex_univ (mem_univ s) (mem_univ t)

/-- Cauchy's estimate and the mean value theorem bound the Lipschitz constant
of the real slice, in the coordinate maximum norm. -/
theorem real_slice_norm_sub_le {ι : Type*} [Fintype ι] {F : (ι → ℂ) → E} {ρ M : ℝ}
    (hρ : 0 < ρ) (hf : DifferentiableOn ℂ F (tube ρ)) (hcap : ∀ z ∈ tube ρ, ‖F z‖ ≤ M)
    (x y : ι → ℝ) : ‖F (fun i => (y i : ℂ)) - F (fun i => (x i : ℂ))‖ ≤ (M / (ρ / 2)) * ‖y - x‖ := by
  by_cases hxy : y = x
  · simp [hxy]
  let d := ‖y - x‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let v (i : ι) := (y i - x i) / d
  have hv (i : ι) : |v i| ≤ 1 := by
    have hi := norm_le_pi_norm (y - x) i
    rw [show v i = (y i - x i) / d from rfl, abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    simpa only [Pi.sub_apply, Real.norm_eq_abs, one_mul] using hi
  let g := F ∘ realLine x v
  have hmap := realLine_strips x v hv ρ
  have hstart : realLine x v 0 = fun i => (x i : ℂ) := by
    funext i
    simp [realLine]
  have hfinish : realLine x v (d : ℂ) = fun i => (y i : ℂ) := by
    funext i
    change (x i : ℂ) + (d : ℂ) * ((v i : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    congr 1
    dsimp only [v]
    field_simp
    ring
  have hb := norm_sub_on_real_line (f := g) hρ
    (hf.comp (differentiable_realLine x v).differentiableOn hmap) (fun z hz => hcap _ (hmap hz)) 0 d
  simpa only [g, Function.comp_apply, Complex.ofReal_zero, hstart, hfinish, sub_zero, Real.norm_of_nonneg hd.le] using hb

end HeatAnalyticRealLipschitz

#print axioms HeatAnalyticRealLipschitz.real_slice_norm_sub_le
