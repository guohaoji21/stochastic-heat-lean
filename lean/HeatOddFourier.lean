import HeatPhysicalGenerator
import HeatPaperAdjoint

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatOddFourier
open MeasureTheory AddCircle SHE CircleHeat DyadicApproximation
open scoped ENNReal ComplexConjugate RealInnerProductSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem circleSine_memLp (n : ℤ) : MemLp (fun x : AddCircle (1 : ℝ) => (fourier n x).im) 2 haarAddCircle := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe _)

def circleSine (n : ℤ) : RealL2 := (circleSine_memLp n).toLp (fun x => (fourier n x).im)

theorem circleSine_ae (n : ℤ) : (circleSine n : AddCircle (1 : ℝ) → ℝ) =ᵐ[haarAddCircle]
    (fun x => (fourier n x).im) := (circleSine_memLp n).coeFn_toLp

theorem coefficient_im_inner (f : RealL2) (n : ℤ) :
    (fourierCoeff (realEmbed f) n).im = -inner ℝ f (circleSine n) := by
  have hi : Integrable (fun x : AddCircle (1 : ℝ) => fourier (-n) x • realEmbed f x) haarAddCircle :=
    ((Lp.memLp (realEmbed f)).integrable (by norm_num)).fourier_smul (-n)
  unfold fourierCoeff
  change Complex.imCLM (∫ x, fourier (-n) x • realEmbed f x ∂haarAddCircle) = _
  rw [← Complex.imCLM.integral_comp_comm hi, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [realEmbed_ae f, circleSine_ae n] with x hf hs
  rw [hf, hs]
  simp [fourier_neg, smul_eq_mul, Complex.mul_im, Real.inner_apply, mul_comm]

theorem odd_coefficient_re_zero (f : HeatRealOddSemigroup.oddSpace) (n : ℤ) :
    (fourierCoeff (realEmbed (f : RealL2)) n).re = 0 := by
  have hodd : HeatCircleReflection.reflect (realEmbed (f : RealL2)) = -realEmbed (f : RealL2) := by
    rw [← HeatRealOddSemigroup.realEmbed_reflection, (HeatRealOddSemigroup.mem_oddSpace _).mp f.property, map_neg]
  have hn : fourierCoeff (realEmbed (f : RealL2)) (-n) = -fourierCoeff (realEmbed (f : RealL2)) n := by
    rw [← HeatCircleReflection.fourierCoeff_reflect, ← fourierBasis_repr, hodd, map_neg]
    simp only [lp.coeFn_neg, Pi.neg_apply, fourierBasis_repr]
  have hr : ∀ᵐ x ∂haarAddCircle, (realEmbed (f : RealL2) x).im = 0 := by
    filter_upwards [realEmbed_ae (f : RealL2)] with x hx
    rw [hx]
    exact Complex.ofReal_im _
  have hc := RealHeat.fourierCoeff_conjugate (realEmbed (f : RealL2)) n
  rw [RealHeat.conjugate_eq_of_real _ hr, hn] at hc
  have he := congrArg Complex.re hc
  simp only [map_neg, Complex.conj_re, Complex.neg_re] at he
  linarith

end HeatOddFourier
#check @HeatOddFourier.circleSine_memLp
#print axioms HeatOddFourier.circleSine_memLp
#check @HeatOddFourier.circleSine_ae
#print axioms HeatOddFourier.circleSine_ae
#check @HeatOddFourier.coefficient_im_inner
#print axioms HeatOddFourier.coefficient_im_inner
#check @HeatOddFourier.odd_coefficient_re_zero
#print axioms HeatOddFourier.odd_coefficient_re_zero
