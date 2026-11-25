import HeatSpectralDerivative
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatGeneratorNecessary
open SHE MeasureTheory AddCircle CircleHeat DyadicApproximation
open HeatOddSurjectivity HeatFoldProbability HeatSpectralDerivative
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev H := Lp ℝ 2 normalizedIntervalMeasure

def coefficientCLM (n : ℤ) : H →L[ℝ] ℂ :=
  (lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n).comp
    ((fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
      (realEmbed.comp ((HeatRealOddSemigroup.oddSpace.subtypeL).comp
        oddEquiv.toLinearIsometry.toContinuousLinearMap)))

theorem coefficientCLM_apply (n : ℤ) (f : H) : coefficientCLM n f = coefficient f n := by
  change fourierBasis.repr (realEmbed ((oddEquiv f : HeatRealOddSemigroup.oddSpace) : RealL2)) n = _
  exact fourierBasis_repr _ n

theorem generator_coordinate (f g : H)
    (hg : HasDerivWithinAt (fun t : ℝ => transportedHeat t f) g (Set.Ici 0) 0)
    (n : ℤ) : coefficient g n =
      ((-((Real.pi * (n : ℝ) / 10)^2) : ℝ) * coefficient f n) := by
  have h := (coefficientCLM n).hasFDerivAt.comp_hasDerivWithinAt 0 hg
  have hs : HasDerivWithinAt (fun t : ℝ => coefficient (transportedHeat t f) n)
      (coefficient g n) (Set.Ici 0) 0 := by
    simpa only [Function.comp_def, coefficientCLM_apply] using h
  have he := (uniqueDiffWithinAt_Ici 0).eq hs (coefficient_derivative f n)
  have he1 := congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) he
  simpa using he1


theorem generator_weighted_summable (f g : H)
    (hg : HasDerivWithinAt (fun t : ℝ => transportedHeat t f) g (Set.Ici 0) 0) :
    Summable (fun n : ℤ => ‖((-((Real.pi * (n : ℝ) / 10)^2) : ℝ) * coefficient f n)‖^2) := by
  have hsum : Summable (fun n : ℤ => ‖coefficient g n‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierBasis_repr, coefficient] using
      (lp.memℓp (fourierBasis.repr (realEmbed ((oddEquiv g : HeatRealOddSemigroup.oddSpace) : RealL2)))).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply hsum.congr
  intro n
  rw [generator_coordinate f g hg n]

end HeatGeneratorNecessary
#check @HeatGeneratorNecessary.coefficientCLM_apply
#print axioms HeatGeneratorNecessary.coefficientCLM_apply
#check @HeatGeneratorNecessary.generator_coordinate
#print axioms HeatGeneratorNecessary.generator_coordinate

#check @HeatGeneratorNecessary.generator_weighted_summable
#print axioms HeatGeneratorNecessary.generator_weighted_summable
