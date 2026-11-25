import HeatDirichletSpectrum
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatSpectralDerivative
open SHE MeasureTheory AddCircle CircleHeat DyadicApproximation
open HeatOddSurjectivity HeatFoldProbability HeatDirichletSpectrum
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def coefficient (f : Lp ℝ 2 normalizedIntervalMeasure) (n : ℤ) : ℂ :=
  fourierCoeff (realEmbed ((oddEquiv f : HeatRealOddSemigroup.oddSpace) : RealL2)) n

theorem coefficient_derivative (f : Lp ℝ 2 normalizedIntervalMeasure) (n : ℤ) :
    HasDerivWithinAt (fun t : ℝ => coefficient (transportedHeat t f) n)
      ((-((Real.pi * (n : ℝ) / 10)^2) : ℝ) * coefficient f n)
      (Set.Ici 0) 0 := by
  let c : ℝ := (Real.pi * (n : ℝ) / 10)^2
  let z : ℂ := coefficient f n
  have hR : HasDerivAt (fun t : ℝ => Real.exp (-t*c)) (-c) 0 := by
    have h := (Real.hasDerivAt_exp (-((0 : ℝ))*c)).comp 0 (((hasDerivAt_id (0 : ℝ)).neg).mul_const c)
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, neg_zero, neg_mul, zero_mul, Real.exp_zero, one_mul] using h
  have hC : HasDerivAt (fun t : ℝ => (Real.exp (-t*c) : ℂ) * z) ((-c : ℝ) * z) 0 := by
    simpa using hR.ofReal_comp.mul_const z
  apply hC.hasDerivWithinAt.congr_of_mem
  · intro t ht
    exact transported_fourier t ht f n
  · exact show (0 : ℝ) ≤ 0 from le_rfl

end HeatSpectralDerivative
#check @HeatSpectralDerivative.coefficient_derivative
#print axioms HeatSpectralDerivative.coefficient_derivative
