import HeatRegularKernel
import HeatControlConvolution
import HeatSliceNorm
import HeatTerminalNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace HeatDecayingConvolutionEnergy

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

private theorem causal_kernel (γ : ℝ) (hγ : 0 < γ) (f : ℝ≥0 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t, ∫⁻ s, HeatRegularKernel.kernel γ ((t : ℝ) - s) * f s
        ∂timeMeasure H ∂timeMeasure H) ≤
      ENNReal.ofReal (HeatRegularKernel.mass γ) * (∫⁻ s, f s ∂timeMeasure H) := by
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (HeatRegularKernel.causal_energy H γ hγ f hf)
  filter_upwards [timeMeasure_ae_mem H] with t ht
  rw [← timeMeasure_restrict ht.2, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with s hs
  by_cases hst : s ≤ t
  · rw [indicator_of_mem (show s ∈ Ioc 0 t from ⟨hs.1, hst⟩)]
  · rw [indicator_of_notMem (show s ∉ Ioc 0 t from fun h => hst h.2)]
    have hreal : ¬ 0 < (t : ℝ) - s := by
      rw [sub_pos]
      exact fun h => hst (by exact_mod_cast h.le)
    simp only [HeatRegularKernel.kernel, indicator_of_notMem (show ((t : ℝ) - s) ∉ Ioi 0 from hreal), zero_mul]

variable (S : ℝ≥0 → E →L[ℝ] E) (Q M : E →L[ℝ] E)
  {γ : ℝ} (hγ : 0 < γ) (hdecay : ∀ t x, ‖Q (S t x)‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖x‖)

omit [CompleteSpace E] [SecondCountableTopology E] in
include hγ hdecay in
/-- The causal convolution kernel has integrated squared energy bounded
uniformly by the input energy and the mass of the decaying kernel. -/
theorem raw_energy (u : ℝ≥0 × Ω → E) (hu : Measurable u) :
    (∫⁻ t, ∫⁻ s, ∫⁻ ω, ENNReal.ofReal
        (‖Q (HeatVolterraKernel.raw S M u (t, (s, ω)))‖ ^ 2) ∂μ ∂timeMeasure H ∂timeMeasure H) ≤
      ENNReal.ofReal (‖M‖ ^ 2 * HeatRegularKernel.mass γ) *
        (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖u (s, ω)‖ ^ 2) ∂μ ∂timeMeasure H) := by
  let input (s : ℝ≥0) := ∫⁻ ω, ENNReal.ofReal (‖u (s, ω)‖ ^ 2) ∂μ
  let c := ENNReal.ofReal (‖M‖ ^ 2)
  have hm : Measurable input :=
    (show Measurable (fun p => ENNReal.ofReal (‖u p‖ ^ 2)) from by fun_prop).lintegral_prod_right'
  let k (t s : ℝ≥0) := HeatRegularKernel.kernel γ ((t : ℝ) - s)
  have hk (t s : ℝ≥0) : k t s ≠ ⊤ := by
    unfold k HeatRegularKernel.kernel
    by_cases h : (t : ℝ) - s ∈ Ioi 0
    · rw [indicator_of_mem h]
      exact ENNReal.ofReal_ne_top
    · rw [indicator_of_notMem h]
      exact ENNReal.zero_ne_top
  have hb (t s : ℝ≥0) (ω : Ω) :
      ENNReal.ofReal (‖Q (HeatVolterraKernel.raw S M u (t, (s, ω)))‖ ^ 2) ≤
        c * k t s * ENNReal.ofReal (‖u (s, ω)‖ ^ 2) := by
    by_cases hst : s < t
    · have hreal : (s : ℝ) < t := by exact_mod_cast hst
      have hn := (hdecay (t - s) (M (u (s, ω)))).trans
        (mul_le_mul_of_nonneg_left (M.le_opNorm _) (Real.exp_nonneg _))
      rw [NNReal.coe_sub hst.le] at hn
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
      unfold k c HeatRegularKernel.kernel
      rw [indicator_of_mem (show ((t : ℝ) - s) ∈ Ioi 0 from sub_pos.mpr hreal),
        ← ENNReal.ofReal_mul (sq_nonneg ‖M‖),
        ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg ‖M‖) (Real.exp_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      simp only [HeatVolterraKernel.raw, ite_eq_left hst]
      refine hsq.trans_eq ?_
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
      have hexp : (2 : ℝ) * (-γ * ((t : ℝ) - s)) = -2 * γ * ((t : ℝ) - s) := by ring
      rw [show ((2 : ℕ) : ℝ) = 2 from rfl, hexp]
      ring
    · simp only [HeatVolterraKernel.raw, ite_eq_right hst, map_zero, norm_zero,
        zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, zero_le]
  calc
    _ ≤ ∫⁻ t, ∫⁻ s, c * k t s * input s ∂timeMeasure H ∂timeMeasure H := by
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro s
      change (∫⁻ ω, ENNReal.ofReal (‖Q (HeatVolterraKernel.raw S M u (t, (s, ω)))‖ ^ 2) ∂μ) ≤
        c * k t s * (∫⁻ ω, ENNReal.ofReal (‖u (s, ω)‖ ^ 2) ∂μ)
      rw [← lintegral_const_mul' (c * k t s) _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hk t s))]
      exact lintegral_mono (hb t s)
    _ = c * (∫⁻ t, ∫⁻ s, k t s * input s ∂timeMeasure H ∂timeMeasure H) := by
      simp_rw [mul_assoc, lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
    _ ≤ c * (ENNReal.ofReal (HeatRegularKernel.mass γ) * (∫⁻ s, input s ∂timeMeasure H)) :=
      mul_le_mul_right (causal_kernel H γ hγ input hm) c
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg ‖M‖)]

variable (F : Filtration ℝ≥0 mΩ) {κ : Type*} [Countable κ]
  (b : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
  (hS : ∀ x, Continuous (fun t => S t x)) (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

local notation "ν" => Measure.trim (energyMeasure μ H) (predictable_le_product F)
local notation "I" => HeatTerminalNaturality.integral F μ H b J
local notation "V" => HeatVolterraSlice.slice F μ H S hS hcontr M

include hγ hdecay in
/-- Decay gives a uniform integrated energy estimate for the actual
stochastic convolution after the spatial map is applied. -/
theorem stochastic (u : Process (E := E) F μ H) :
    (∫ t, ‖(Q.compLpL 2 μ) ((I).integral (V t u))‖ ^ 2 ∂timeMeasure H) ≤
      ‖M‖ ^ 2 * HeatRegularKernel.mass γ * ‖u‖ ^ 2 := by
  let N (t : ℝ≥0) := (Q.compLpL 2 μ) ((I).integral (V t u))
  have hc : Continuous N := (Q.compLpL 2 μ).continuous.comp
    (HeatVolterraContinuity.integral_continuous F μ H S hS hcontr M I u)
  have hi : Integrable (fun t => ‖N t‖ ^ 2) (timeMeasure H) := by
    apply (integrable_const ((‖Q.compLpL 2 μ‖ * (‖M‖ * ‖u‖)) ^ 2)).mono'
      (hc.norm.pow 2).aestronglyMeasurable
    apply Eventually.of_forall
    intro t
    change ‖‖N t‖ ^ 2‖ ≤ (‖Q.compLpL 2 μ‖ * (‖M‖ * ‖u‖)) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    refine ((Q.compLpL 2 μ).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [(I).integral.norm_map]
    exact HeatSliceNorm.bound F μ H S hS hcontr M u t
  have henergy (t : ℝ≥0) :
      ENNReal.ofReal (‖N t‖ ^ 2) =
        ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖Q (HeatVolterraKernel.raw S M u (t, (s, ω)))‖ ^ 2)
          ∂μ ∂timeMeasure H := by
    let w : Process (E := E) F μ H := by
      letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      exact (Q.compLpL 2 ν) (V t u)
    have hcomm : N t = (I).integral w := HeatTerminalNaturality.commutes F μ H b J Q (V t u)
    rw [hcomm, (I).integral.norm_map, process_lintegral_energy]
    have hw : (w : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] fun p => Q (V t u p) := by
      let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      exact ae_eq_of_ae_eq_trim (Q.coeFn_compLpL (V t u))
    have he := hw.trans ((HeatVolterraSlice.slice_ae F μ H S hS hcontr M t u).fun_comp Q)
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod he] with s hs
    apply lintegral_congr_ae
    filter_upwards [hs] with ω hω
    exact congrArg (fun x : E => ENNReal.ofReal (‖x‖ ^ 2)) hω
  change (∫ t, ‖N t‖ ^ 2 ∂timeMeasure H) ≤ _
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)) (sq_nonneg _))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _),
    ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)),
    process_lintegral_energy F μ H u]
  simp_rw [henergy]
  have hu : Measurable (u : ℝ≥0 × Ω → E) :=
    ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
  exact raw_energy μ H S Q M hγ hdecay u hu

include hγ hdecay hS hcontr in
/-- The deterministic forcing term has a uniform integrated bound with
the same mass of the decaying kernel. -/
theorem forcing (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ H)) :
    (∫⁻ t, ∫⁻ ω, ENNReal.ofReal (‖Q (HeatControlConvolution.value H S f t ω)‖ ^ 2)
        ∂μ ∂timeMeasure H) ≤
      ENNReal.ofReal ((H : ℝ) * HeatRegularKernel.mass γ) *
        (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖f (s, ω)‖ ^ 2) ∂μ ∂timeMeasure H) := by
  let r (t : ℝ≥0) (p : ℝ≥0 × Ω) := HeatControlConvolution.raw S f t p
  let e (t : ℝ≥0) (p : ℝ≥0 × Ω) := ENNReal.ofReal (‖Q (r t p)‖ ^ 2)
  have hm (t : ℝ≥0) : Measurable (r t) := HeatControlConvolution.raw_measurable S hS hcontr f hf t
  have he (t : ℝ≥0) : Measurable (e t) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      ((Q.continuous.measurable.comp (hm t)).norm.pow_const 2)
  have hmass : (timeMeasure H).real univ = (H : ℝ) := by
    rw [Measure.real, timeMeasure_mass]
    exact ENNReal.toReal_ofReal H.property
  have ht (t : ℝ≥0) :
      (∫⁻ ω, ENNReal.ofReal (‖Q (HeatControlConvolution.value H S f t ω)‖ ^ 2) ∂μ) ≤
        ENNReal.ofReal (H : ℝ) * (∫⁻ s, ∫⁻ ω, e t (s, ω) ∂μ ∂timeMeasure H) := by
    have hs : (∫⁻ s, ∫⁻ ω, e t (s, ω) ∂μ ∂timeMeasure H) =
        ∫⁻ ω, ∫⁻ s, e t (s, ω) ∂timeMeasure H ∂μ :=
      lintegral_lintegral_swap (f := fun s ω => e t (s, ω)) (he t).aemeasurable
    rw [hs, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [HeatControlConvolution.time_memLp μ H f hf hfi] with ω hω
    have hr : MemLp (fun s => r t (s, ω)) 2 (timeMeasure H) := by
      apply hω.norm.mono' (((hm t).comp
        (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable)
      exact Eventually.of_forall (fun s => HeatControlConvolution.raw_bound S hcontr f t (s, ω))
    have hQ : MemLp (fun s => Q (r t (s, ω))) 2 (timeMeasure H) :=
      Q.lipschitzWith.comp_memLp (map_zero Q) hr
    change ENNReal.ofReal (‖Q (∫ s, r t (s, ω) ∂timeMeasure H)‖ ^ 2) ≤
      ENNReal.ofReal (H : ℝ) * (∫⁻ s, ENNReal.ofReal (‖Q (r t (s, ω))‖ ^ 2) ∂timeMeasure H)
    rw [← Q.integral_comp_comm (hr.integrable one_le_two),
      ← ofReal_integral_eq_lintegral_ofReal hQ.norm.integrable_sq
        (Eventually.of_forall fun _ => sq_nonneg _)]
    have hb := IntegralEnergy.norm_integral_sq (timeMeasure H) _ hQ
    rw [hmass] at hb
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq (ENNReal.ofReal_mul H.property)
  have hr := raw_energy μ H S Q (ContinuousLinearMap.id ℝ E) hγ hdecay f hf
  have hId : ‖ContinuousLinearMap.id ℝ E‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (ContinuousLinearMap.id ℝ E))
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)) 2
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (H : ℝ) * (∫⁻ s, ∫⁻ ω, e t (s, ω) ∂μ ∂timeMeasure H)
        ∂timeMeasure H := lintegral_mono ht
    _ = ENNReal.ofReal (H : ℝ) * (∫⁻ t, ∫⁻ s, ∫⁻ ω, e t (s, ω) ∂μ ∂timeMeasure H
        ∂timeMeasure H) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (H : ℝ) * (ENNReal.ofReal (HeatRegularKernel.mass γ) *
        (∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖f (s, ω)‖ ^ 2) ∂μ ∂timeMeasure H)) := by
      apply mul_le_mul_right _ _
      refine hr.trans (mul_le_mul_left ?_ _)
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_right hId (HeatRegularKernel.mass_nonneg γ hγ)).trans_eq (one_mul _)
    _ = _ := by
      have h : ENNReal.ofReal ((H : ℝ) * HeatRegularKernel.mass γ) =
          ENNReal.ofReal (H : ℝ) * ENNReal.ofReal (HeatRegularKernel.mass γ) :=
        ENNReal.ofReal_mul H.property
      rw [h, mul_assoc]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
include hγ hdecay in
theorem orbit (x : E) :
    (∫⁻ t, ENNReal.ofReal (‖Q (S t x)‖ ^ 2) ∂timeMeasure H) ≤
      ENNReal.ofReal (HeatRegularKernel.mass γ) * ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [timeMeasure_lintegral]
  calc
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) H, HeatRegularKernel.kernel γ t * ENNReal.ofReal (‖x‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [HeatRegularKernel.kernel, indicator_of_mem (show t ∈ Ioi 0 from ht.1),
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hn := hdecay t.toNNReal x
      rw [Real.coe_toNNReal _ ht.1.le] at hn
      refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq ?_
      rw [mul_pow, ← Real.exp_nat_mul]
      have he : (2 : ℝ) * (-γ * t) = -2 * γ * t := by ring
      rw [show ((2 : ℕ) : ℝ) = 2 from rfl, he]
    _ ≤ ∫⁻ t : ℝ, HeatRegularKernel.kernel γ t * ENNReal.ofReal (‖x‖ ^ 2) :=
      lintegral_mono' Measure.restrict_le_self (le_refl _)
    _ = _ := by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, HeatRegularKernel.kernel_mass γ hγ]

end HeatDecayingConvolutionEnergy

#print axioms HeatDecayingConvolutionEnergy.raw_energy
#print axioms HeatDecayingConvolutionEnergy.stochastic
#print axioms HeatDecayingConvolutionEnergy.forcing
#print axioms HeatDecayingConvolutionEnergy.orbit
