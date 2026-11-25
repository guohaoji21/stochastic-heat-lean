import HeatDampedMomentBound
import HeatConjugateSlices
import HeatMomentAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatMomentInvariant
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

include hcontr in
theorem forcing_bound {γ : ℝ} (hγ : 0≤γ) (g : E) (t : ℝ≥0) :
    ‖Real.exp (-γ*(t:ℝ)) • S t g‖≤‖g‖ := by
  have he : Real.exp (-γ*(t:ℝ))≤1 := Real.exp_le_one_iff.mpr (by nlinarith [t.property])
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (hcontr t g) (Real.exp_pos _).le).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg g))

include hS hcontr in
theorem maps_ball (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B)
    {γ D : ℝ} (hγ : 0<γ) (hD : 0≤D)
    (hsmall : (2:ℝ)^15*(B:ℝ)*(‖M‖^2*HeatRegularKernel.mass γ)^8≤1/2)
    (g : E) (h₀ : (2:ℝ)^16*‖g‖^16≤D) :
    Set.MapsTo (PredictableExponential.conjugate F μ H γ
      (HeatVolterraForcing.orbit F μ H S hS hcontr g)
      (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I))
      (HeatMomentBall.Ball D) (HeatMomentBall.Ball D) := by
  intro u hu
  change ∀ᵐ t ∂timeMeasure H, HeatMomentBall.moment (μ:=μ) (fun ω =>
    PredictableExponential.conjugate F μ H γ (HeatVolterraForcing.orbit F μ H S hS hcontr g)
      (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I) u (t,ω)) ≤ ENNReal.ofReal D
  filter_upwards [HeatConjugateSlices.representation F μ H S hS hcontr M hsem I γ g u,
    timeMeasure_ae_mem H] with t hrep ht
  rw [HeatMomentBall.moment_congr hrep]
  let v := I.integral (HeatDampedSlice.input F μ H S hS hcontr M γ t u)
  have hsum := HeatMomentAlgebra.add_bound μ (fun _ => Real.exp (-γ*(t:ℝ)) • S t g)
    (v : Ω → E) measurable_const (Lp.stronglyMeasurable v).measurable
  have hforce := HeatMomentAlgebra.constant_bound μ (Real.exp (-γ*(t:ℝ)) • S t g) (‖g‖^16)
    (pow_le_pow_left₀ (norm_nonneg _) (forcing_bound S hcontr hγ.le g t) 16)
  have hnoise := HeatDampedMomentBound.input_moment F μ H S hS hcontr M I B hB hγ hD u hu t ht.2
  refine hsum.trans ((mul_le_mul_right (add_le_add hforce hnoise) _).trans ?_)
  have hL : 0≤‖M‖^2*HeatRegularKernel.mass γ := mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)
  have hc : 0≤(B:ℝ)*(‖M‖^2*HeatRegularKernel.mass γ)^8*D := by positivity
  rw [←ENNReal.ofReal_add (pow_nonneg (norm_nonneg _) 16) hc,
    ←ENNReal.ofReal_mul (by positivity : 0≤(2:ℝ)^15)]
  apply ENNReal.ofReal_le_ofReal
  have hmul := mul_le_mul_of_nonneg_right hsmall hD
  norm_num only [show (2:ℝ)^16=65536 by norm_num,show (2:ℝ)^15=32768 by norm_num] at h₀ hmul ⊢
  nlinarith only [h₀,hmul]

end HeatMomentInvariant
#check @HeatMomentInvariant.forcing_bound
#print axioms HeatMomentInvariant.forcing_bound
#check @HeatMomentInvariant.maps_ball
#print axioms HeatMomentInvariant.maps_ball
