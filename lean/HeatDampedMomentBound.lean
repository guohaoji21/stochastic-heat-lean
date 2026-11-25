import HeatDampedSlice
import HeatMomentBall
import SHEStochastic.ScalarLipschitzItoMoment

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatDampedMomentBound
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

include hS hcontr in
theorem input_moment (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B)
    {γ : ℝ} (hγ : 0<γ) {D : ℝ} (hD : 0≤D) (u : Process (E := E) F μ H)
    (hu : u ∈ HeatMomentBall.Ball D) (t : ℝ≥0) (ht : t≤H) :
    HeatMomentBall.moment (μ:=μ) (I.integral (HeatDampedSlice.input F μ H S hS hcontr M γ t u)) ≤
      ENNReal.ofReal ((B:ℝ)*(‖M‖^2*HeatRegularKernel.mass γ)^8*D) := by
  let k := fun s : ℝ≥0 => ENNReal.ofReal (‖M‖^2)*HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ))
  let f := fun p : ℝ≥0 × Ω => ENNReal.ofReal (‖u p‖^2)
  have hk : Measurable k := measurable_const.mul ((HeatRegularKernel.measurable γ).comp
    (measurable_const.sub NNReal.continuous_coe.measurable))
  have hf : Measurable f :=
    ((((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable.norm.pow_const 2).ennreal_ofReal)
  have hM : ∀ᵐ s ∂timeMeasure H, (∫⁻ ω, (f (s,ω))^8 ∂μ) ≤ ENNReal.ofReal D := by
    filter_upwards [hu] with s hs
    have he (ω : Ω) : (f (s,ω))^8=ENNReal.ofReal (‖u (s,ω)‖^16) := by
      dsimp only [f]
      rw [←ENNReal.ofReal_pow (sq_nonneg _),←pow_mul]
    simpa only [he,HeatMomentBall.moment] using hs
  have ha : ∀ᵐ p ∂energyMeasure μ H,
      ENNReal.ofReal (‖HeatDampedSlice.input F μ H S hS hcontr M γ t u p‖^2) ≤ k p.1*f p := by
    filter_upwards [HeatDampedSlice.input_ae F μ H S hS hcontr M γ t u] with p hp
    rw [hp]
    exact HeatDampedSlice.raw_bound F μ H S hcontr M γ t u p
  have hh := SHEStochastic.ScalarLipschitzItoMoment.moment_of_density I B hB
    (HeatDampedSlice.input F μ H S hS hcontr M γ t u) k hk f hf (ENNReal.ofReal D) hM ha
  have hkm : (∫⁻ s, k s ∂timeMeasure H) ≤ ENNReal.ofReal (‖M‖^2*HeatRegularKernel.mass γ) := by
    dsimp only [k]
    have hmeas : Measurable (fun s : ℝ≥0 => HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ))) :=
      (HeatRegularKernel.measurable γ).comp (measurable_const.sub NNReal.continuous_coe.measurable)
    rw [lintegral_const_mul'' (ENNReal.ofReal (‖M‖^2)) hmeas.aemeasurable,
      ENNReal.ofReal_mul (sq_nonneg ‖M‖)]
    exact mul_le_mul_right (HeatRegularMomentKernel.mass_bound H hγ ht) _
  refine hh.trans ((mul_le_mul_left (mul_le_mul_right (pow_le_pow_left' hkm 8) _) _).trans_eq ?_)
  have hL : 0≤‖M‖^2*HeatRegularKernel.mass γ := mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)
  rw [←ENNReal.ofReal_pow (n:=8) hL,←ENNReal.ofReal_coe_nnreal (p:=B)]
  have hfirst : ENNReal.ofReal (B:ℝ)*ENNReal.ofReal ((‖M‖^2*HeatRegularKernel.mass γ)^8) =
      ENNReal.ofReal ((B:ℝ)*(‖M‖^2*HeatRegularKernel.mass γ)^8) :=
    (ENNReal.ofReal_mul (q := (‖M‖^2*HeatRegularKernel.mass γ)^8) B.property).symm
  have hprod : 0≤(B:ℝ)*(‖M‖^2*HeatRegularKernel.mass γ)^8 := mul_nonneg B.property (pow_nonneg hL 8)
  exact (congrArg (fun z => z*ENNReal.ofReal D) hfirst).trans (ENNReal.ofReal_mul (q:=D) hprod).symm


end HeatDampedMomentBound
#check @HeatDampedMomentBound.input_moment
#print axioms HeatDampedMomentBound.input_moment
