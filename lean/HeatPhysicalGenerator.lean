import HeatGeneratorSufficient
import HeatGeneratorDissipative

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatPhysicalGenerator
open HeatIntervalNormalization HeatGeneratorDissipative HeatSpectralDerivative

def coefficient (f : Base) (n : ℤ) : ℂ :=
  HeatSpectralDerivative.coefficient (measureEquiv f) n

theorem measureEquiv_heat (t : ℝ) (f : Base) :
    measureEquiv (paperHeat t f) = HeatOddSurjectivity.transportedHeat t (measureEquiv f) := by
  simp only [paperHeat_apply, HeatOddSurjectivity.transportedHeat_apply, paperOddEquiv,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.apply_symm_apply]

theorem generator_to_normalized (f g : Base) (h : generator f g) :
    HasDerivWithinAt (fun t : ℝ => HeatOddSurjectivity.transportedHeat t (measureEquiv f))
      (measureEquiv g) (Set.Ici 0) 0 := by
  have hs := measureEquiv.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt 0 h
  simpa only [generator, Function.comp_def, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, measureEquiv_heat] using hs

theorem generator_from_normalized (f g : Base)
    (h : HasDerivWithinAt (fun t : ℝ => HeatOddSurjectivity.transportedHeat t (measureEquiv f))
      (measureEquiv g) (Set.Ici 0) 0) : generator f g := by
  have hs := measureEquiv.symm.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt 0 h
  have he (t : ℝ) : measureEquiv.symm (HeatOddSurjectivity.transportedHeat t (measureEquiv f)) = paperHeat t f := by
    rw [← measureEquiv_heat, measureEquiv.symm_apply_apply]
  simpa only [generator, Function.comp_def, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, he, measureEquiv.symm_apply_apply] using hs

theorem generator_iff_coefficients (f g : Base) : generator f g ↔
    ∀ n : ℤ, coefficient g n =
      ((-((Real.pi * (n : ℝ) / 10)^2) : ℝ) * coefficient f n) := by
  constructor
  · intro h
    exact (HeatGeneratorSufficient.generator_iff_coefficients _ _).mp (generator_to_normalized f g h)
  · intro h
    exact generator_from_normalized f g ((HeatGeneratorSufficient.generator_iff_coefficients _ _).mpr h)

end HeatPhysicalGenerator
#check @HeatPhysicalGenerator.measureEquiv_heat
#print axioms HeatPhysicalGenerator.measureEquiv_heat
#check @HeatPhysicalGenerator.generator_to_normalized
#print axioms HeatPhysicalGenerator.generator_to_normalized
#check @HeatPhysicalGenerator.generator_from_normalized
#print axioms HeatPhysicalGenerator.generator_from_normalized
#check @HeatPhysicalGenerator.generator_iff_coefficients
#print axioms HeatPhysicalGenerator.generator_iff_coefficients
