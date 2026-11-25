import HeatVolterraModel
import HeatRegularKernel
import SHEStochastic.KernelItoWeighted

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatVolterraEnergy
open MeasureTheory Set SHE SHE.PredictableL2 HeatVolterraKernel
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
include hS hcontr

theorem causal_lintegral (γ : ℝ) (u v : ℝ≥0 × Ω → E) (t : ℝ≥0) (ht : t ≤ H) :
    (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      ‖raw S M u (t,(s,ω))-raw S M v (t,(s,ω))‖^2) ∂μ ∂timeMeasure H) =
    ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      ‖raw S M u (t,(s,ω))-raw S M v (t,(s,ω))‖^2) ∂μ ∂timeMeasure t := by
  rw [← timeMeasure_restrict ht, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with s hs
  by_cases hst : s ≤ t
  · rw [Set.indicator_of_mem (show s ∈ Ioc 0 t from ⟨hs.1,hst⟩)]
  · rw [Set.indicator_of_notMem (show s ∉ Ioc 0 t from fun hh => hst hh.2)]
    have hn : ¬ s < t := not_lt.mpr (le_of_not_ge hst)
    simp [raw, hn]

theorem raw_difference_bound (u v : ℝ≥0 × Ω → E) (t s : ℝ≥0) (ω : Ω) (hst : s < t) :
    ‖raw S M u (t,(s,ω))-raw S M v (t,(s,ω))‖^2 ≤ ‖M‖^2 * ‖u (s,ω)-v (s,ω)‖^2 := by
  simp only [raw, if_pos hst]
  rw [← map_sub, ← map_sub]
  have hn := (hcontr (t-s) (M (u (s,ω)-v (s,ω)))).trans (M.le_opNorm _)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg M) (norm_nonneg (u (s,ω)-v (s,ω))))).mpr hn
  simpa only [mul_pow] using hs

theorem weighted_point_bound (γ : ℝ) (u v : ℝ≥0 × Ω → E) (t s : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖raw S M u (t,(s,ω))-raw S M v (t,(s,ω))‖^2) ≤
      ENNReal.ofReal (‖M‖^2) * HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ)) *
        ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2) := by
  by_cases hst : s < t
  · have hτ : 0 < (t:ℝ)-(s:ℝ) := sub_pos.mpr (by exact_mod_cast hst)
    rw [HeatRegularKernel.kernel, Set.indicator_of_mem (show (t:ℝ)-(s:ℝ) ∈ Ioi (0:ℝ) from hτ),
      ← ENNReal.ofReal_mul (sq_nonneg ‖M‖),
      ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg ‖M‖) (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-2*γ*(t:ℝ)) = Real.exp (-2*γ*((t:ℝ)-(s:ℝ)))*Real.exp (-2*γ*(s:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hb := mul_le_mul_of_nonneg_left (raw_difference_bound S hS hcontr M u v t s ω hst)
      (mul_nonneg (Real.exp_pos (-2*γ*((t:ℝ)-(s:ℝ)))).le (Real.exp_pos (-2*γ*(s:ℝ))).le)
    convert hb using 1 <;> ring
  · simp only [raw, if_neg hst, sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
      mul_zero, ENNReal.ofReal_zero, zero_le]

theorem expected_energy (γ : ℝ) (hγ : 0 < γ) (u v : ℝ≥0 × Ω → E) (hu : Measurable u) (hv : Measurable v) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (-2*γ*(p.1:ℝ))*‖raw S M u p-raw S M v p‖^2)
      ∂SHE.HaarKernelL2Approximation.measure μ H) ≤
      ENNReal.ofReal (‖M‖^2 * HeatRegularKernel.mass γ) *
        (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2) ∂μ ∂timeMeasure H) := by
  let F : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖u (s,ω)-v (s,ω)‖^2) ∂μ
  let C := ENNReal.ofReal (‖M‖^2)
  have hF : Measurable F := by
    have hm : Measurable (fun p : ℝ≥0 × Ω => ENNReal.ofReal
        (Real.exp (-2*γ*(p.1:ℝ))*‖u p-v p‖^2)) := by fun_prop
    exact hm.lintegral_prod_right'
  have hm : Measurable (fun p : ℝ≥0 × (ℝ≥0 × Ω) => ENNReal.ofReal
      (Real.exp (-2*γ*(p.1:ℝ))*‖raw S M u p-raw S M v p‖^2)) := by
    have hru := raw_measurable S M hS hcontr u hu
    have hrv := raw_measurable S M hS hcontr v hv
    fun_prop
  rw [SHE.HaarKernelL2Approximation.triple_lintegral μ H hm]
  have he : (∫⁻ t, ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      ‖raw S M u (t,(s,ω))-raw S M v (t,(s,ω))‖^2) ∂μ ∂timeMeasure H ∂timeMeasure H) =
      ∫⁻ t, ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      ‖raw S M u (t,(s,ω))-raw S M v (t,(s,ω))‖^2) ∂μ ∂timeMeasure t ∂timeMeasure H := by
    apply lintegral_congr_ae
    filter_upwards [timeMeasure_ae_mem H] with t ht
    exact causal_lintegral μ H S hS hcontr M γ u v t ht.2
  rw [he]
  have hbound : (∫⁻ t, ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      ‖raw S M u (t,(s,ω))-raw S M v (t,(s,ω))‖^2) ∂μ ∂timeMeasure t ∂timeMeasure H) ≤
      ∫⁻ t, ∫⁻ s, C*HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure t ∂timeMeasure H := by
    apply lintegral_mono
    intro t
    apply lintegral_mono
    intro s
    have hk : HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ)) ≠ ∞ := by
      unfold HeatRegularKernel.kernel
      by_cases h0 : (t:ℝ)-(s:ℝ) ∈ Ioi (0:ℝ)
      · rw [Set.indicator_of_mem h0]
        exact ENNReal.ofReal_ne_top
      · rw [Set.indicator_of_notMem h0]
        exact ENNReal.zero_ne_top
    dsimp only [F]
    rw [← lintegral_const_mul' (C*HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ))) _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hk)]
    apply lintegral_mono
    intro ω
    exact weighted_point_bound S hS hcontr M γ u v t s ω
  calc
    _ ≤ _ := hbound
    _ = C*(∫⁻ t, ∫⁻ s, HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure t ∂timeMeasure H) := by
      simp_rw [mul_assoc, lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
    _ ≤ C*(ENNReal.ofReal (HeatRegularKernel.mass γ)*(∫⁻ s, F s ∂timeMeasure H)) :=
      mul_le_mul_right (HeatRegularKernel.causal_energy H γ hγ F hF) C
    _ = _ := by
      dsimp only [C,F]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg ‖M‖)]

end HeatVolterraEnergy
#check @HeatVolterraEnergy.causal_lintegral
#print axioms HeatVolterraEnergy.causal_lintegral
#check @HeatVolterraEnergy.raw_difference_bound
#print axioms HeatVolterraEnergy.raw_difference_bound
#check @HeatVolterraEnergy.weighted_point_bound
#print axioms HeatVolterraEnergy.weighted_point_bound
#check @HeatVolterraEnergy.expected_energy
#print axioms HeatVolterraEnergy.expected_energy
