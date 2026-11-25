import HeatAnalyticOpenPropagation
import SHE.ProcessEnergy

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace HeatAnalyticObservedNorm

open MeasureTheory Set UnitAddTorus HeatAnalyticOpenPropagation
open HeatTorusGaussian (wrap)
open HeatGevreyFourierExtension (tube)
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [CompleteSpace E]

private theorem norm_sq_energy (g : UnitAddTorus ι → E) {μ : Measure (UnitAddTorus ι)}
    (hg : MemLp g 2 μ) : (∫⁻ x, energy g x ∂μ) = ENNReal.ofReal (‖hg.toLp g‖ ^ 2) := by
  rw [SHE.PredictableL2.realLp_norm_sq,
    ofReal_integral_eq_lintegral_ofReal (Lp.memLp (hg.toLp g)).norm.integrable_sq
      (ae_of_all _ (fun _ => sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp only [energy, hx]

/-- The quantitative analytic continuation estimate in actual `L²` norms,
with any physical period and normalized Haar measure on its unit parametrization. -/
theorem squared_norm_interpolation {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty)
    {P ρ : ℝ} (hP : 0 < P) (hρ : 0 < ρ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : (ι → ℂ) → E) (g : UnitAddTorus ι → E) (hg : MemLp g 2 volume) (M : ℝ), 0 < M →
        DifferentiableOn ℂ F (tube ρ) → (∀ z ∈ tube ρ, ‖F z‖ ≤ M) →
        (∀ (z : ι → ℂ) (m : ι → ℤ), F (z + fun i => (P : ℂ) * (m i : ℂ)) = F z) →
        (∀ x : ι → ℝ, g (wrap x) = F (fun i => ((P * x i : ℝ) : ℂ))) →
        ‖hg.toLp g‖ ^ 2 ≤ C * M ^ 2 * ((‖(hg.restrict O).toLp g‖ ^ 2 / M ^ 2) ^ θ) := by
  obtain ⟨C, θ, hC, hθ, hθ1, hprop⟩ := squared_energy_interpolation (E := E) hO hOne (div_pos hρ hP)
  refine ⟨C, θ, hC, hθ, hθ1, fun F g hg M hM hF hcap hper hreal => ?_⟩
  let A : (ι → ℂ) →L[ℂ] (ι → ℂ) := (P : ℂ) • ContinuousLinearMap.id ℂ _
  have hA (z : ι → ℂ) (i : ι) : A z i = (P : ℂ) * z i := rfl
  have hmaps : MapsTo A (tube (ρ / P)) (tube ρ) := by
    intro z hz
    apply mem_iInter.mpr
    intro i
    have hzi : |(z i).im| < ρ / P := abs_lt.mpr (mem_iInter.mp hz i)
    apply abs_lt.mp
    change |(A z i).im| < ρ
    simp only [hA, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_pos hP]
    exact (mul_comm P _).trans_lt ((lt_div_iff₀ hP).mp hzi)
  have hper' (z : ι → ℂ) (m : ι → ℤ) :
      (F ∘ A) (z + fun i => (m i : ℂ)) = (F ∘ A) z := by
    change F (A (z + fun i => (m i : ℂ))) = F (A z)
    rw [map_add, show A (fun i => (m i : ℂ)) = fun i => (P : ℂ) * (m i : ℂ) from funext (hA _), hper]
  have hreal' (x : ι → ℝ) : g (wrap x) = (F ∘ A) (fun i => (x i : ℂ)) := by
    rw [hreal]
    congr 1
    funext i
    rw [hA, Complex.ofReal_mul]
  have h := hprop (F ∘ A) g M hM (hF.comp A.differentiable.differentiableOn hmaps)
    (fun z hz => hcap _ (hmaps hz)) hper' hreal'
  rw [norm_sq_energy g hg, norm_sq_energy g (hg.restrict O), ENNReal.toReal_ofReal (sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Weighted Fourier energy implies quantitative observation in actual L²
norms on the unit torus. The bound is uniform over the frequency support. -/
theorem weighted_fourier_interpolation {O : Set (UnitAddTorus ι)} (hO : IsOpen O)
    (hOne : O.Nonempty) {a : ℝ} (ha : 0 < a) :
    ∃ C K θ : ℝ, 0 < C ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (c : (ι → ℤ) → E) (g : UnitAddTorus ι → E) (hg : MemLp g 2 volume) (M : ℝ), 0 < M →
        (∀ S : Finset (ι → ℤ), ∑ k ∈ S, Real.exp (2 * a * HeatGevreyFourierExtension.weight k)
          * ‖c k‖ ^ 2 ≤ M ^ 2) →
        (∀ x : ι → ℝ, g (wrap x) = ∑' k, mFourier k (wrap x) • c k) →
        ‖hg.toLp g‖ ^ 2 ≤ C * (M * K) ^ 2 * ((‖(hg.restrict O).toLp g‖ ^ 2 / (M * K) ^ 2) ^ θ) := by
  obtain ⟨C, θ, hC, hθ, hθ₁, hprop⟩ :=
    squared_norm_interpolation (E := E) (P := 1) hO hOne one_pos
      (show 0 < a / (4 * Real.pi) by positivity)
  let s := ∑' k : ι → ℤ, Real.exp (-(a / 2) * HeatGevreyFourierExtension.weight k)
  let K := s + 1
  have hs : 0 ≤ s := tsum_nonneg (fun _ => Real.exp_nonneg _)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, K, θ, hC, hK, hθ, hθ₁, fun c g hg M hM hcap hreal => ?_⟩
  obtain ⟨F, hF, hFreal, hper, hbound⟩ :=
    HeatGevreyFourierExtension.exists_energy_extension c M a hM.le ha hcap
  refine hprop F g hg (M * K) (mul_pos hM hK) hF (fun z hz => (hbound z hz).trans ?_) ?_ ?_
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hM.le
  · simpa only [Complex.ofReal_one, one_mul] using hper
  · intro x
    simpa only [one_mul] using (hreal x).trans (hFreal x).symm

end HeatAnalyticObservedNorm

#print axioms HeatAnalyticObservedNorm.squared_norm_interpolation
#print axioms HeatAnalyticObservedNorm.weighted_fourier_interpolation
