import HeatConvolutionIncrementBound
import HeatMildSolution
import HeatMomentBall
import SHEStochastic.ScalarLipschitzItoMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatConvolutionTimeMoment
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : E,
    ‖S δ (S τ x)-S τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

def coefficient (B : ℝ≥0) (R : ℝ) : ℝ :=
  (B:ℝ)*(6*((H:ℝ)^(1/2:ℝ)*‖M‖^2)*(H:ℝ)^(1/4:ℝ))^8*R

include hS hcontr hsem hsmooth in
theorem increment (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B)
    (u : Process (E := E) F μ H) (R : ℝ) (hR : 0≤R) (hu : u∈HeatMomentBall.Ball R)
    {s t : ℝ≥0} (hst : s≤t) (ht : t≤H) :
    HeatMomentBall.moment (μ:=μ) (fun ω =>
      I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω-
      I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M s u) ω) ≤
      ENNReal.ofReal (coefficient H M B R*((t:ℝ)-(s:ℝ))^2) := by
  let K : ℝ := (H:ℝ)^(1/2:ℝ)*‖M‖^2
  let a := HeatVolterraSlice.slice F μ H S hS hcontr M t u
  let b := HeatVolterraSlice.slice F μ H S hS hcontr M s u
  let f := fun p : ℝ≥0 × Ω => ENNReal.ofReal (‖u p‖^2)
  have hf : Measurable f := (((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable.norm.pow_const 2).ennreal_ofReal
  have hM : ∀ᵐ r ∂timeMeasure H, (∫⁻ ω, (f (r,ω))^8 ∂μ) ≤ ENNReal.ofReal R := by
    filter_upwards [hu] with r hr
    have he (ω : Ω) : (f (r,ω))^8=ENNReal.ofReal (‖u (r,ω)‖^16) := by
      dsimp only [f]
      rw [←ENNReal.ofReal_pow (sq_nonneg _),←pow_mul]
    simpa only [he,HeatMomentBall.moment] using hr
  have hd : ∀ᵐ p ∂energyMeasure μ H, ENNReal.ofReal (‖(a-b) p‖^2)≤
      SHEStochastic.ScalarLipschitzAgeDensity.density K s t p.1*f p := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub a b),
      HeatVolterraSlice.slice_ae F μ H S hS hcontr M t u,
      HeatVolterraSlice.slice_ae F μ H S hS hcontr M s u] with p hp ha hb
    rw [hp]
    simp only [Pi.sub_apply]
    dsimp only [a,b]
    rw [ha,hb]
    exact HeatConvolutionIncrementBound.density_bound S hcontr M hsem hsmooth u hst ht p
  have hh := SHEStochastic.ScalarLipschitzItoMoment.moment_of_density I B hB (a-b)
    (SHEStochastic.ScalarLipschitzAgeDensity.density K s t)
    (SHEStochastic.ScalarLipschitzAgeDensity.measurable K s t) f hf (ENNReal.ofReal R) hM hd
  have he : I.integral (a-b) =ᵐ[μ] (fun ω => I.integral a ω-I.integral b ω) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  rw [←HeatMomentBall.moment_congr he]
  have hK : 0≤K := by positivity
  have hmass := SHEStochastic.ScalarLipschitzAgeDensity.mass hK hst ht
  refine hh.trans ((mul_le_mul_left (mul_le_mul_right (pow_le_pow_left' hmass 8) _) _).trans_eq ?_)
  let L : ℝ := 6*K*(H:ℝ)^(1/4:ℝ)
  let δ : ℝ := (t:ℝ)-(s:ℝ)
  have hδ : 0≤δ := sub_nonneg.mpr (by exact_mod_cast hst)
  have hL : 0≤L := by positivity
  change (B:ℝ≥0∞)*ENNReal.ofReal (L*δ^(1/4:ℝ))^8*ENNReal.ofReal R =
    ENNReal.ofReal ((B:ℝ)*L^8*R*δ^2)
  rw [←ENNReal.ofReal_pow (n:=8) (mul_nonneg hL (Real.rpow_nonneg hδ _)),
    ←ENNReal.ofReal_coe_nnreal (p:=B)]
  have hp : (L*δ^(1/4:ℝ))^8=L^8*δ^2 := by
    rw [mul_pow,←Real.rpow_mul_natCast hδ]
    norm_num only [Nat.cast_ofNat,show (1/4:ℝ)*8=2 by norm_num,Real.rpow_two]
  rw [hp]
  rw [ENNReal.ofReal_mul (p:=(B:ℝ)*L^8*R) (q:=δ^2) (by positivity),
    ENNReal.ofReal_mul (p:=(B:ℝ)*L^8) (q:=R) (by positivity),
    ENNReal.ofReal_mul (p:=(B:ℝ)) (q:=L^8) B.property,
    ENNReal.ofReal_mul (p:=L^8) (q:=δ^2) (by positivity)]
  ring

end HeatConvolutionTimeMoment
#check @HeatConvolutionTimeMoment.increment
#print axioms HeatConvolutionTimeMoment.increment
