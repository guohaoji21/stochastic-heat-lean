import HeatDirichletIdentification
import HeatWeakDirichletAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatFourierFrame
open MeasureTheory EllipticPdes HeatIntervalNormalization HeatWeakDirichlet
open SHE CircleHeat DyadicApproximation AddCircle HeatPhysicalGenerator FiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

def vector (n : ℤ) : Base := -(Real.sqrt 10)⁻¹ • HeatSineH01.sine (Real.pi*(n:ℝ)/10)
def coordinate (n : ℤ) : Base →L[ℝ] ℝ := innerSL ℝ (vector n)
def rate (n : ℤ) : ℝ := (Real.pi*(n:ℝ)/10)^2

theorem coordinate_coefficient (n : ℤ) (x : Base) : coordinate n x=(coefficient x n).im := by
  change inner ℝ (-(Real.sqrt 10)⁻¹ • HeatSineH01.sine (Real.pi*(n:ℝ)/10)) x=_
  rw [real_inner_smul_left,real_inner_comm x,HeatSineFourier.coefficient_im_pairing]
  have hs : Real.sqrt 10≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

theorem parseval (x : Base) : ‖x‖^2=∑' n : ℤ,(coordinate n x)^2 := by
  have hn := CircleHeat.norm_sq_fourier (realEmbed (paperOddEquiv x : RealL2))
  rw [realEmbed_norm_eq] at hn
  change ‖paperOddEquiv x‖^2=_ at hn
  rw [paperOddEquiv.norm_map] at hn
  rw [hn]
  apply tsum_congr
  intro n
  rw [coordinate_coefficient]
  have hr := HeatOddFourier.odd_coefficient_re_zero (paperOddEquiv x) n
  change ‖coefficient x n‖^2=(coefficient x n).im^2
  change (coefficient x n).re=0 at hr
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,hr,pow_two]

theorem eigen (n : ℤ) : weakLaplacian (vector n) (-(rate n) • vector n) := by
  have hg := HeatSineWeakEigen.sine_weak_eigenpair _ (HeatSineWeakEigen.frequency_boundary n)
  have hs := HeatWeakDirichletAlgebra.smul (-(Real.sqrt 10)⁻¹) _ _ hg
  simpa only [vector,rate,smul_smul,mul_comm] using hs

theorem rate_nonnegative (n : ℤ) : 0≤rate n := sq_nonneg _

end HeatFourierFrame
#check @HeatFourierFrame.coordinate_coefficient
#print axioms HeatFourierFrame.coordinate_coefficient
#check @HeatFourierFrame.parseval
#print axioms HeatFourierFrame.parseval
#check @HeatFourierFrame.eigen
#print axioms HeatFourierFrame.eigen
#check @HeatFourierFrame.rate_nonnegative
#print HeatFourierFrame.rate_nonnegative
#print axioms HeatFourierFrame.rate_nonnegative
