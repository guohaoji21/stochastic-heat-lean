import HeatSineWeakEigen
import HeatSineFourier

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatDirichletIdentification
open HeatIntervalNormalization HeatWeakDirichlet HeatGeneratorDissipative HeatPhysicalGenerator
open HeatSineWeakEigen HeatSineFourier HeatOddFourier
open scoped RealInnerProductSpace

theorem weak_fourier_identity (f g : Base) (h : weakLaplacian f g) (n : ℤ) :
    coefficient g n = ((-((Real.pi*(n:ℝ)/10)^2) : ℝ) : ℂ) * coefficient f n := by
  have hm := sine_modal_identity f g h n
  rw [coefficient_im_pairing, coefficient_im_pairing] at hm
  have hroot : Real.sqrt 10 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hi : (coefficient g n).im = -((Real.pi*(n:ℝ)/10)^2) * (coefficient f n).im := by
    apply mul_left_cancel₀ hroot
    nlinarith only [hm]
  have hrf := odd_coefficient_re_zero (paperOddEquiv f) n
  have hrg := odd_coefficient_re_zero (paperOddEquiv g) n
  change (coefficient f n).re = 0 at hrf
  change (coefficient g n).re = 0 at hrg
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hrf, hrg,
      mul_zero, zero_mul, sub_self]
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hi

theorem weak_to_generator (f g : Base) (h : weakLaplacian f g) : generator f g := by
  apply (generator_iff_coefficients f g).mpr
  exact weak_fourier_identity f g h

theorem generator_iff_weakLaplacian (f g : Base) : generator f g ↔ weakLaplacian f g :=
  generator_eq_weak_of_inclusion weak_to_generator f g

end HeatDirichletIdentification
#check @HeatDirichletIdentification.weak_fourier_identity
#print axioms HeatDirichletIdentification.weak_fourier_identity
#check @HeatDirichletIdentification.weak_to_generator
#print axioms HeatDirichletIdentification.weak_to_generator
#check @HeatDirichletIdentification.generator_iff_weakLaplacian
#print axioms HeatDirichletIdentification.generator_iff_weakLaplacian
