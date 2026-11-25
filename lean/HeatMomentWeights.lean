import HeatRegularMomentKernel
import HeatVolterraFixedPoint

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatMomentWeights
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

theorem exists_weight (C B : ℝ) : ∃ γ : ℝ, 0<γ ∧ C*HeatRegularKernel.mass γ≤1/4 ∧
    (2:ℝ)^15*B*(C*HeatRegularKernel.mass γ)^8≤1/2 := by
  have h₁ : Tendsto (fun γ => C*HeatRegularKernel.mass γ) atTop (𝓝 0) := by
    simpa only [mul_zero] using HeatRegularMomentKernel.mass_tends_zero.const_mul C
  have h₂ : Tendsto (fun γ => (2:ℝ)^15*B*(C*HeatRegularKernel.mass γ)^8) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (8:ℕ)≠0),mul_zero] using (h₁.pow 8).const_mul ((2:ℝ)^15*B)
  obtain ⟨γ,hγ,h₁,h₂⟩ := ((eventually_ge_atTop (1:ℝ)).and
    ((h₁.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).and
      (h₂.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))))).exists
  exact ⟨γ,lt_of_lt_of_le (by norm_num) hγ,h₁.le,h₂.le⟩

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem lipschitz {γ : ℝ} (hγ : 0<γ) (hsmall : ‖M‖^2*HeatRegularKernel.mass γ≤1/4)
    (forcing : Process (E := E) F μ H) :
    LipschitzWith (1/2) (PredictableExponential.conjugate F μ H γ forcing
      (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  let N := HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I
  have he := HeatVolterraFixedPoint.weighted_energy F μ H S hS hcontr M hsem I γ hγ
    (PredictableExponential.scale F μ H γ u) (PredictableExponential.scale F μ H γ v)
  rw [←PredictableExponential.sub,PredictableExponential.cancel] at he
  have hCm : 0≤‖M‖^2*HeatRegularKernel.mass γ :=
    mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)
  rw [←ENNReal.ofReal_mul hCm] at he
  have hr := ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCm (sq_nonneg ‖u-v‖))).mp he).trans
    (mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u-v‖))
  have hd : PredictableExponential.conjugate F μ H γ forcing N u -
      PredictableExponential.conjugate F μ H γ forcing N v =
      PredictableExponential.scale F μ H (-γ)
        (N (PredictableExponential.scale F μ H γ u)-N (PredictableExponential.scale F μ H γ v)) := by
    rw [PredictableExponential.conjugate,PredictableExponential.conjugate,
      ←PredictableExponential.sub,add_sub_add_left_eq_sub]
  rw [dist_eq_norm,dist_eq_norm,hd]
  change ‖PredictableExponential.scale F μ H (-γ)
    (N (PredictableExponential.scale F μ H γ u)-N (PredictableExponential.scale F μ H γ v))‖≤(1/2:ℝ)*‖u-v‖
  nlinarith [norm_nonneg (PredictableExponential.scale F μ H (-γ)
    (N (PredictableExponential.scale F μ H γ u)-N (PredictableExponential.scale F μ H γ v))),norm_nonneg (u-v)]

end HeatMomentWeights
#check @HeatMomentWeights.exists_weight
#print axioms HeatMomentWeights.exists_weight
#check @HeatMomentWeights.lipschitz
#print axioms HeatMomentWeights.lipschitz
