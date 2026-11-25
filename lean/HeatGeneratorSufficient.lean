import HeatGeneratorNecessary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatGeneratorSufficient
open SHE MeasureTheory AddCircle CircleHeat DyadicApproximation
open HeatOddSurjectivity HeatFoldProbability HeatSpectralDerivative HeatGeneratorNecessary
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem coefficient_ext (f g : H) (h : ∀ n, coefficient f n = coefficient g n) : f = g := by
  apply oddEquiv.injective
  apply Subtype.ext
  have he : realEmbed ((oddEquiv f : HeatRealOddSemigroup.oddSpace) : RealL2) =
      realEmbed ((oddEquiv g : HeatRealOddSemigroup.oddSpace) : RealL2) := by
    apply fourierBasis.repr.injective
    apply lp.ext
    funext n
    simpa only [fourierBasis_repr, coefficient] using h n
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← FiniteHaar.realEmbed_norm_eq, map_sub, he, sub_self, norm_zero]

theorem orbit_integral (f g : H)
    (hfg : ∀ n : ℤ, coefficient g n =
      ((-((Real.pi * (n : ℝ) / 10)^2) : ℝ) * coefficient f n))
    (t : ℝ) (ht : 0 ≤ t) :
    transportedHeat t f - f = ∫ s in (0 : ℝ)..t, transportedHeat s g := by
  apply coefficient_ext
  intro n
  let c : ℝ := (Real.pi * (n : ℝ) / 10)^2
  let z : ℂ := coefficient f n
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => (Real.exp (-r*c) : ℂ) * z)
      ((Real.exp (-s*c) : ℂ) * coefficient g n) s := by
    have hR : HasDerivAt (fun r : ℝ => Real.exp (-r*c)) (Real.exp (-s*c) * (-c)) s := by
      have hRaw := (Real.hasDerivAt_exp (-s*c)).comp s
        (((hasDerivAt_id s).neg).mul_const c)
      simpa only [Function.comp_def, Pi.neg_apply, id_eq, neg_mul, one_mul] using hRaw
    have hC : HasDerivAt (fun r : ℝ => (Real.exp (-r*c) : ℂ) * z)
        (((Real.exp (-s*c) * (-c) : ℝ) : ℂ) * z) s :=
      hR.ofReal_comp.mul_const z
    have hcg : coefficient g n = ((-c : ℝ) : ℂ) * z := hfg n
    have heq : (((Real.exp (-s*c) * (-c) : ℝ) : ℂ) * z) =
        (Real.exp (-s*c) : ℂ) * coefficient g n := by
      rw [Complex.ofReal_mul, hcg, mul_assoc]
    rw [heq] at hC
    exact hC
  have hc : Continuous (fun s : ℝ => (Real.exp (-s*c) : ℂ) * coefficient g n) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 t)
  have hI := (coefficientCLM n).intervalIntegral_comp_comm (μ := volume) ((transportedHeat_continuous g).intervalIntegrable 0 t)
  rw [← coefficientCLM_apply n (transportedHeat t f - f),
    ← coefficientCLM_apply n (∫ s in (0 : ℝ)..t, transportedHeat s g)]
  rw [map_sub, ← hI]
  simp only [coefficientCLM_apply]
  rw [show coefficient (transportedHeat t f) n = (Real.exp (-t*c) : ℂ) * z from
    HeatDirichletSpectrum.transported_fourier t ht f n]
  rw [← show (Real.exp (-(0 : ℝ)*c) : ℂ) * z = coefficient f n by simp [z]]
  rw [← he]
  apply intervalIntegral.integral_congr
  intro s hs
  exact (HeatDirichletSpectrum.transported_fourier s ((Set.mem_Icc.mp ((Set.uIcc_of_le ht) ▸ hs)).1) g n).symm

theorem generator_of_coefficients (f g : H)
    (hfg : ∀ n : ℤ, coefficient g n =
      ((-((Real.pi * (n : ℝ) / 10)^2) : ℝ) * coefficient f n)) :
    HasDerivWithinAt (fun t : ℝ => transportedHeat t f) g (Set.Ici 0) 0 := by
  have hc := transportedHeat_continuous g
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hz : transportedHeat 0 g = g := by rw [transportedHeat_zero]; rfl
  rw [hz] at hd
  have hs := hd.add_const f
  have hs' : HasDerivWithinAt (fun t : ℝ => (∫ s in (0 : ℝ)..t, transportedHeat s g) + f) g (Set.Ici 0) 0 :=
    hs.hasDerivWithinAt
  apply hs'.congr_of_mem
  · intro t ht
    exact (sub_eq_iff_eq_add.mp (orbit_integral f g hfg t ht))
  · exact Set.mem_Ici.mpr le_rfl

theorem generator_iff_coefficients (f g : H) :
    HasDerivWithinAt (fun t : ℝ => transportedHeat t f) g (Set.Ici 0) 0 ↔
      ∀ n : ℤ, coefficient g n =
        ((-((Real.pi * (n : ℝ) / 10)^2) : ℝ) * coefficient f n) :=
  ⟨fun h n => generator_coordinate f g h n, generator_of_coefficients f g⟩

end HeatGeneratorSufficient
#check @HeatGeneratorSufficient.coefficient_ext
#print axioms HeatGeneratorSufficient.coefficient_ext
#check @HeatGeneratorSufficient.orbit_integral
#print axioms HeatGeneratorSufficient.orbit_integral
#check @HeatGeneratorSufficient.generator_of_coefficients
#print axioms HeatGeneratorSufficient.generator_of_coefficients

#check @HeatGeneratorSufficient.generator_iff_coefficients
#print axioms HeatGeneratorSufficient.generator_iff_coefficients
