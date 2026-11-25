import HeatOddSurjectivity

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatDirichletSpectrum
open SHE MeasureTheory AddCircle CircleHeat DyadicApproximation
open HeatOddSurjectivity HeatFoldProbability
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem weight_rescaled (t : ℝ) (ht : 0 ≤ t) (n : ℤ) :
    heatWeight (t / 400) n = (Real.exp (-t * (Real.pi * (n : ℝ) / 10)^2) : ℂ) := by
  simp only [heatWeight, max_eq_left (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 400))]
  congr 2
  ring

theorem transported_fourier (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 normalizedIntervalMeasure) (n : ℤ) :
    fourierCoeff (realEmbed ((oddEquiv (transportedHeat t f) : HeatRealOddSemigroup.oddSpace) : RealL2)) n =
      (Real.exp (-t * (Real.pi * (n : ℝ) / 10)^2) : ℂ) *
        fourierCoeff (realEmbed ((oddEquiv f : HeatRealOddSemigroup.oddSpace) : RealL2)) n := by
  rw [transportedHeat_apply, oddEquiv.apply_symm_apply]
  change fourierCoeff (realEmbed ((HeatRealOddSemigroup.oddHeat (t/400) (oddEquiv f) :
    HeatRealOddSemigroup.oddSpace) : RealL2)) n = _
  rw [HeatRealOddSemigroup.oddHeat_coe, SHE.RealHeat.realEmbed_realHeat, heat_fourierCoeff,
    weight_rescaled t ht n]

end HeatDirichletSpectrum
#check @HeatDirichletSpectrum.weight_rescaled
#print axioms HeatDirichletSpectrum.weight_rescaled
#check @HeatDirichletSpectrum.transported_fourier
#print axioms HeatDirichletSpectrum.transported_fourier
