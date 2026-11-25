import HeatConjugateForcing
import HeatMomentInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatForcedMomentInvariant
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem maps_ball (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B)
    {γ R D : ℝ} (hγ : 0<γ) (hR : 0≤R) (hD : 0≤D)
    (hsmall : (2:ℝ)^15*(B:ℝ)*(‖M‖^2*HeatRegularKernel.mass γ)^8≤1/2)
    (A : Process (E := E) F μ H) (hA : A∈HeatMomentBall.Ball R) (h₀ : (2:ℝ)^16*R≤D) :
    Set.MapsTo (PredictableExponential.conjugate F μ H γ A
      (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I))
      (HeatMomentBall.Ball D) (HeatMomentBall.Ball D) := by
  intro u hu
  change ∀ᵐ t ∂timeMeasure H, HeatMomentBall.moment (μ:=μ) (fun ω =>
    PredictableExponential.conjugate F μ H γ A
      (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I) u (t,ω))≤ENNReal.ofReal D
  filter_upwards [HeatConjugateForcing.representation F μ H S hS hcontr M hsem I γ A u,
    hA,timeMeasure_ae_mem H] with t hrep hAt ht
  rw [HeatMomentBall.moment_congr hrep]
  let v := I.integral (HeatDampedSlice.input F μ H S hS hcontr M γ t u)
  have hAm : Measurable (fun ω => A (t,ω)) :=
    (((Lp.stronglyMeasurable A).mono (predictable_le_product F)).measurable).comp (measurable_const.prodMk measurable_id)
  have hsum := HeatMomentAlgebra.add_bound μ (fun ω => Real.exp (-γ*(t:ℝ)) • A (t,ω))
    (v : Ω → E) (measurable_const.smul hAm) (Lp.stronglyMeasurable v).measurable
  have he : Real.exp (-γ*(t:ℝ))≤1 := Real.exp_le_one_iff.mpr (by nlinarith [t.property])
  have hforce : HeatMomentBall.moment (μ:=μ) (fun ω => Real.exp (-γ*(t:ℝ)) • A (t,ω))≤ENNReal.ofReal R := by
    apply le_trans (lintegral_mono (fun ω => ?_)) hAt
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (norm_nonneg _) _ 16
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)
  have hnoise := HeatDampedMomentBound.input_moment F μ H S hS hcontr M I B hB hγ hD u hu t ht.2
  refine hsum.trans ((mul_le_mul_right (add_le_add hforce hnoise) _).trans ?_)
  have hL : 0≤‖M‖^2*HeatRegularKernel.mass γ := mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)
  have hc : 0≤(B:ℝ)*(‖M‖^2*HeatRegularKernel.mass γ)^8*D := by positivity
  rw [←ENNReal.ofReal_add hR hc,←ENNReal.ofReal_mul (by positivity : 0≤(2:ℝ)^15)]
  apply ENNReal.ofReal_le_ofReal
  have hmul := mul_le_mul_of_nonneg_right hsmall hD
  norm_num only [show (2:ℝ)^16=65536 by norm_num,show (2:ℝ)^15=32768 by norm_num] at h₀ hmul ⊢
  nlinarith only [h₀,hmul]

end HeatForcedMomentInvariant
#check @HeatForcedMomentInvariant.maps_ball
#print HeatForcedMomentInvariant.maps_ball
#print axioms HeatForcedMomentInvariant.maps_ball
