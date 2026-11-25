import HeatConvolutionAlgebra
import HeatVolterraForcing
import HeatControlConvolution
import SHE.PredictableExponentialIterates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatVolterraUniformEnergy

open Filter MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s + t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

def stabilityConstant : ℝ := 2 * Real.exp (2 * (2 * ‖M‖ ^ 2 + 1) * (H : ℝ))

/-- An a priori bound in the ordinary predictable norm for the actual
fixed point on its full time horizon. -/
theorem fixed_point_bound (f u : Process (E := E) F μ H)
    (hu : u = f + HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u) :
    ‖u‖ ≤ stabilityConstant H M * ‖f‖ := by
  let γ : ℝ := 2 * ‖M‖ ^ 2 + 1
  let N := HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I
  let weight := PredictableExponential.scale (E := E) F μ H (-γ)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hs : ‖M‖ ^ 2 * HeatRegularKernel.mass γ ≤ 1 / 4 := by
    rw [HeatRegularKernel.mass, mul_one_div, div_le_iff₀ (by positivity : 0 < 2 * γ)]
    dsimp [γ]
    linarith
  have hp : 0 ≤ ‖M‖ ^ 2 * HeatRegularKernel.mass γ :=
    mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)
  have he := HeatVolterraFixedPoint.weighted_energy F μ H S hS hcontr M hsem I γ hγ u 0
  rw [HeatConvolutionAlgebra.zero F μ H S hS hcontr M hsem I, sub_zero, sub_zero,
    ← ENNReal.ofReal_mul hp] at he
  have hrs := ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hp (sq_nonneg ‖weight u‖))).mp he).trans
    (mul_le_mul_of_nonneg_right hs (sq_nonneg ‖weight u‖))
  have hn : ‖weight (N u)‖ ≤ (1 / 2 : ℝ) * ‖weight u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    convert hrs using 1
    ring
  have hadd : weight u = weight f + weight (N u) := by
    have h := congrArg weight hu
    rw [show weight (f + N u) = weight f + weight (N u) from
      PredictableExponential.add F μ H (-γ) f (N u)] at h
    exact h
  have ht : ‖weight u‖ ≤ 2 * ‖weight f‖ := by
    have hb := norm_add_le (weight f) (weight (N u))
    rw [← hadd] at hb
    linarith
  have h1 := PredictableExponentialIterates.scale_norm F μ H γ (weight u)
  rw [show PredictableExponential.scale F μ H γ (weight u) = u from
      PredictableExponential.cancel' F μ H γ u, abs_of_pos hγ] at h1
  have h2 := PredictableExponentialIterates.scale_norm F μ H (-γ) f
  rw [abs_neg, abs_of_pos hγ] at h2
  change ‖weight f‖ ≤ _ at h2
  calc
    ‖u‖ ≤ Real.exp (γ * (H : ℝ)) * ‖weight u‖ := h1
    _ ≤ Real.exp (γ * (H : ℝ)) * (2 * (Real.exp (γ * (H : ℝ)) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))) (Real.exp_nonneg _)
    _ = stabilityConstant H M * ‖f‖ := by
      rw [stabilityConstant, show 2 * (2 * ‖M‖ ^ 2 + 1) * (H : ℝ) =
        γ * (H : ℝ) + γ * (H : ℝ) from by dsimp [γ]; ring, Real.exp_add]
      ring

omit [CompleteSpace E] in
include hS hcontr in
theorem orbit_energy (g : E) :
    ‖HeatVolterraForcing.orbit F μ H S hS hcontr g‖ ^ 2 ≤ (H : ℝ) * ‖g‖ ^ 2 := by
  let a := HeatVolterraForcing.orbit F μ H S hS hcontr g
  have ha : ‖a‖ ^ 2 = ∫ p, ‖a p‖ ^ 2 ∂energyMeasure μ H := subsigma_norm_sq _ _ _
  let : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  change ‖a‖ ^ 2 ≤ _
  have he : (∫ p, ‖a p‖ ^ 2 ∂energyMeasure μ H) =
      ∫ p : ℝ≥0 × Ω, ‖S p.1 g‖ ^ 2 ∂energyMeasure μ H :=
    integral_congr_ae ((HeatVolterraForcing.orbit_ae F μ H S hS hcontr g).fun_comp
      (fun x : E => ‖x‖ ^ 2))
  rw [ha, he]
  have hb : (∫ p : ℝ≥0 × Ω, ‖S p.1 g‖ ^ 2 ∂energyMeasure μ H) ≤
      ∫ _ : ℝ≥0 × Ω, ‖g‖ ^ 2 ∂energyMeasure μ H := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) (integrable_const _)
    exact Eventually.of_forall fun p => pow_le_pow_left₀ (norm_nonneg _) (hcontr p.1 g) 2
  refine hb.trans_eq ?_
  rw [integral_const, smul_eq_mul, Measure.real]
  change (((timeMeasure H).prod μ) univ).toReal * ‖g‖ ^ 2 = _
  rw [← Set.univ_prod_univ, Measure.prod_prod, timeMeasure_mass, measure_univ, mul_one]
  exact congrArg (fun r : ℝ => r * ‖g‖ ^ 2) (ENNReal.toReal_ofReal H.property)

include hS hcontr in
theorem control_energy (f : ℝ≥0 × Ω → E) (hf : Measurable f)
    (hfi : MemLp f 2 (energyMeasure μ H)) (a : Process (E := E) F μ H)
    (ha : ∀ᵐ t ∂timeMeasure H, (fun ω => a (t, ω)) =ᵐ[μ] HeatControlConvolution.value H S f t) :
    ‖a‖ ^ 2 ≤ (H : ℝ) ^ 2 * ∫ p, ‖f p‖ ^ 2 ∂energyMeasure μ H := by
  have hp (t : ℝ≥0) : (∫ ω, ‖HeatControlConvolution.value H S f t ω‖ ^ 2 ∂μ) ≤
        (H : ℝ) * ∫ p, ‖f p‖ ^ 2 ∂energyMeasure μ H := by
    have hh := hfi.norm.integrable_sq.integral_prod_right.const_mul (H : ℝ)
    have he : (∫ p, ‖f p‖ ^ 2 ∂energyMeasure μ H) =
        ∫ ω, ∫ s, ‖f (s, ω)‖ ^ 2 ∂timeMeasure H ∂μ := integral_prod_symm _ hfi.norm.integrable_sq
    rw [he, ← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hh
    filter_upwards [HeatControlConvolution.time_memLp μ H f hf hfi] with ω hω
    exact HeatControlConvolution.energy_pointwise H S hS hcontr f hf ω hω t
  rw [process_integral_energy]
  have he : (fun t => ∫ ω, ‖a (t, ω)‖ ^ 2 ∂μ) =ᵐ[timeMeasure H]
      fun t => ∫ ω, ‖HeatControlConvolution.value H S f t ω‖ ^ 2 ∂μ := by
    filter_upwards [ha] with t ht
    exact integral_congr_ae (ht.fun_comp (fun x : E => ‖x‖ ^ 2))
  rw [integral_congr_ae he]
  calc
    _ ≤ ∫ _ : ℝ≥0, (H : ℝ) * ∫ p, ‖f p‖ ^ 2 ∂energyMeasure μ H ∂timeMeasure H :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
        (integrable_const _) (Eventually.of_forall hp)
    _ = _ := by
      have hm : (timeMeasure H).real univ = (H : ℝ) := by
        rw [Measure.real, timeMeasure_mass]
        exact ENNReal.toReal_ofReal H.property
      rw [integral_const, smul_eq_mul, hm]
      ring

end HeatVolterraUniformEnergy

#print axioms HeatVolterraUniformEnergy.fixed_point_bound
#print axioms HeatVolterraUniformEnergy.orbit_energy
#print axioms HeatVolterraUniformEnergy.control_energy
