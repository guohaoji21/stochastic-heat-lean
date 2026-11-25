import HeatSineH01
import HeatOddFourier

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatSineFourier
open MeasureTheory AddCircle HeatSineH01 HeatIntervalNormalization
open HeatCircleIntervalCoordinates HeatOddEmbedding HeatFoldProbability HeatOddSurjectivity
open SHE CircleHeat DyadicApproximation HeatOddFourier
open scoped ENNReal RealInnerProductSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem fourier_im_coordinate (n : ℤ) (x : AddCircle (1 : ℝ)) :
    (fourier n x).im = orientation x * Real.sin ((Real.pi*(n:ℝ)/10)*position x) := by
  have hx : ((coordinate x : ℝ) : AddCircle (1 : ℝ)) = x := AddCircle.coe_equivIoc
  have he : (fourier n x).im = Real.sin (2*Real.pi*(n:ℝ)*coordinate x) := by
    have hfour : fourier n x = Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(coordinate x:ℂ)/(1:ℂ)) := by
      calc
        _ = fourier n ((coordinate x : ℝ) : AddCircle (1 : ℝ)) := congrArg (fun y => fourier n y) hx.symm
        _ = _ := fourier_coe_apply
    rw [hfour]
    have hr : (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(coordinate x:ℂ)/(1:ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have hi : (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(coordinate x:ℂ)/(1:ℂ)).im =
        2*Real.pi*(n:ℝ)*coordinate x := by simp [Complex.mul_re, Complex.mul_im]
    rw [Complex.exp_im, hr, hi, Real.exp_zero, one_mul]
  rw [he]
  unfold orientation position
  split_ifs with hθ
  · rw [abs_of_nonneg hθ, one_mul]
    congr 1
    ring
  · rw [abs_of_neg (lt_of_not_ge hθ)]
    rw [show (Real.pi*(n:ℝ)/10)*(20*(-coordinate x)) = -(2*Real.pi*(n:ℝ)*coordinate x) by ring,
      Real.sin_neg]
    ring

theorem normalizedSine_ae (k : ℝ) :
    (measureEquiv (sine k) : ℝ → ℝ) =ᵐ[normalizedIntervalMeasure]
      (fun x => Real.sqrt 10 * Real.sin (k*x)) := by
  have hac : normalizedIntervalMeasure ≪ volume.restrict HeatWeakDirichlet.domain := by
    change (ENNReal.ofReal (1/10 : ℝ) • volume.restrict HeatWeakDirichlet.domain) ≪ _
    exact Measure.smul_absolutelyContinuous
  have hs := (sine_ae k).filter_mono hac.ae_le
  change ((Real.sqrt 10 • transfer (sine k) : Normalized) : ℝ → ℝ) =ᵐ[normalizedIntervalMeasure] _
  filter_upwards [Lp.coeFn_smul (Real.sqrt 10) (transfer (sine k)), transfer_ae (sine k), hs]
    with x hm ht hx
  rw [hm]
  simp only [Pi.smul_apply, ht, hx, smul_eq_mul]

theorem sine_image (n : ℤ) :
    (paperOddEquiv (sine (Real.pi*(n:ℝ)/10)) : RealL2) = Real.sqrt 10 • circleSine n := by
  change (oddEquiv (measureEquiv (sine (Real.pi*(n:ℝ)/10))) : RealL2) = _
  rw [oddEquiv_apply, intoOdd_coe]
  apply Lp.ext
  have hs := position_measurePreserving.quasiMeasurePreserving.ae (normalizedSine_ae (Real.pi*(n:ℝ)/10))
  filter_upwards [embedding_ae (measureEquiv (sine (Real.pi*(n:ℝ)/10))), hs,
    Lp.coeFn_smul (Real.sqrt 10) (circleSine n), circleSine_ae n] with x he hs hm hc
  rw [he, hs, hm]
  simp only [Pi.smul_apply, hc, smul_eq_mul]
  rw [fourier_im_coordinate]
  ring

theorem coefficient_im_pairing (f : Base) (n : ℤ) :
    inner ℝ f (sine (Real.pi*(n:ℝ)/10)) =
      -(Real.sqrt 10) * (HeatPhysicalGenerator.coefficient f n).im := by
  rw [← paperOddEquiv.inner_map_map]
  change inner ℝ (paperOddEquiv f : RealL2) (paperOddEquiv (sine (Real.pi*(n:ℝ)/10)) : RealL2) = _
  rw [sine_image, inner_smul_right]
  have h := coefficient_im_inner (paperOddEquiv f : RealL2) n
  change (HeatPhysicalGenerator.coefficient f n).im = -inner ℝ (paperOddEquiv f : RealL2) (circleSine n) at h
  rw [show inner ℝ (paperOddEquiv f : RealL2) (circleSine n) = -(HeatPhysicalGenerator.coefficient f n).im by linarith]
  ring

end HeatSineFourier
#check @HeatSineFourier.fourier_im_coordinate
#print axioms HeatSineFourier.fourier_im_coordinate
#check @HeatSineFourier.normalizedSine_ae
#print axioms HeatSineFourier.normalizedSine_ae
#check @HeatSineFourier.sine_image
#print axioms HeatSineFourier.sine_image
#check @HeatSineFourier.coefficient_im_pairing
#print axioms HeatSineFourier.coefficient_im_pairing
