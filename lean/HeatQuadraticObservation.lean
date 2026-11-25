import HeatWeightedIncrementMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatQuadraticObservation
open MeasureTheory Filter
variable {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pointwise (c x y : ℝ) (A D : E) :
    ‖c • (x • A+y • D)‖^2=c^2*(x^2*‖A‖^2+(2*inner ℝ A D)*(x*y)+y^2*‖D‖^2) := by
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,norm_add_sq_real]
  simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,real_inner_smul_left,real_inner_smul_right]
  ring

theorem expectation (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (c : ℝ) (A D : E) :
    (∫ ω,‖c • (X ω • A+Y ω • D)‖^2 ∂μ)=c^2*((∫ ω,X ω^2 ∂μ)*‖A‖^2+
      (2*inner ℝ A D)*(∫ ω,X ω*Y ω ∂μ)+(∫ ω,Y ω^2 ∂μ)*‖D‖^2) := by
  have hXX : Integrable (fun ω => X ω^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using hX.norm.integrable_sq
  have hYY : Integrable (fun ω => Y ω^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using hY.norm.integrable_sq
  have hXY : Integrable (fun ω => X ω*Y ω) μ := hX.integrable_mul hY
  have he : (fun ω => ‖c • (X ω • A+Y ω • D)‖^2)=
      fun ω => c^2*(X ω^2*‖A‖^2+(2*inner ℝ A D)*(X ω*Y ω)+Y ω^2*‖D‖^2) :=
    funext fun ω => pointwise c (X ω) (Y ω) A D
  rw [he,integral_const_mul]
  let a := fun ω => X ω^2*‖A‖^2
  let b := fun ω => (2*inner ℝ A D)*(X ω*Y ω)
  let d := fun ω => Y ω^2*‖D‖^2
  have ha : Integrable a μ := hXX.mul_const _
  have hb : Integrable b μ := hXY.const_mul _
  have hd : Integrable d μ := hYY.mul_const _
  congr 1
  calc
    (∫ ω,a ω+b ω+d ω ∂μ) = (∫ ω,a ω+b ω ∂μ)+(∫ ω,d ω ∂μ) := integral_add (ha.add hb) hd
    _ = ((∫ ω,a ω ∂μ)+(∫ ω,b ω ∂μ))+(∫ ω,d ω ∂μ) :=
      congrArg (fun v : ℝ => v+(∫ ω,d ω ∂μ)) (integral_add ha hb)
    _ = _ := by
      dsimp only [a,b,d]
      rw [integral_mul_const,integral_const_mul,integral_mul_const]


end HeatQuadraticObservation
#check @HeatQuadraticObservation.expectation
#print HeatQuadraticObservation.expectation
#print axioms HeatQuadraticObservation.expectation
