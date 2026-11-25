import SHE.RealHeat

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatCircleReflection
open SHE MeasureTheory AddCircle CircleHeat
open scoped NNReal ENNReal ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def reflect (f : CircleL2) : CircleL2 :=
  Lp.compMeasurePreserving (fun x : AddCircle (1 : ℝ) => -x)
    (Measure.measurePreserving_neg haarAddCircle) f

theorem reflect_ae (f : CircleL2) : reflect f =ᵐ[haarAddCircle] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem fourierCoeff_reflect (f : CircleL2) (n : ℤ) :
    fourierCoeff (reflect f) n = fourierCoeff f (-n) := by
  rw [fourierCoeff_congr_ae (reflect_ae f)]
  unfold fourierCoeff
  simp only [neg_neg]
  rw [← integral_neg_eq_self (fun x : AddCircle (1 : ℝ) => fourier n x • f x) haarAddCircle]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp [fourier_apply, smul_neg, neg_smul]

theorem reflect_heat (t : ℝ) (f : CircleL2) : reflect (heat t f) = heat t (reflect f) := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr, fourierCoeff_reflect, heat_fourierCoeff]
  congr 1
  simp only [heatWeight, Int.cast_neg, mul_neg, neg_sq]

theorem heat_preserves_odd (t : ℝ) (f : CircleL2) (hf : reflect f = -f) :
    reflect (heat t f) = -(heat t f) := by
  rw [reflect_heat, hf, map_neg]


def reflectionCLM : CircleL2 →L[ℂ] CircleL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : AddCircle (1 : ℝ) => -x)
    (Measure.measurePreserving_neg haarAddCircle)).toContinuousLinearMap

def oddSpace : Submodule ℂ CircleL2 :=
  (reflectionCLM + ContinuousLinearMap.id ℂ CircleL2).toLinearMap.ker

theorem mem_oddSpace (f : CircleL2) : f ∈ oddSpace ↔ reflect f = -f := by
  change reflect f + f = 0 ↔ reflect f = -f
  exact add_eq_zero_iff_eq_neg

theorem oddSpace_closed : IsClosed (oddSpace : Set CircleL2) :=
  (reflectionCLM + ContinuousLinearMap.id ℂ CircleL2).isClosed_ker

theorem odd_heat_invariant (t : ℝ) (f : CircleL2) (hf : f ∈ oddSpace) : heat t f ∈ oddSpace :=
  (mem_oddSpace _).2 (heat_preserves_odd t f ((mem_oddSpace _).1 hf))

def oddHeat (t : ℝ) : oddSpace →L[ℂ] oddSpace :=
  ((heat t).domRestrict oddSpace).codRestrict oddSpace
    (fun f => odd_heat_invariant t f f.property)

theorem oddHeat_coe (t : ℝ) (f : oddSpace) : (oddHeat t f : CircleL2) = heat t f := rfl

theorem oddHeat_zero : oddHeat 0 = ContinuousLinearMap.id ℂ oddSpace := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp [oddHeat_coe, heat_zero]

theorem oddHeat_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    oddHeat (s+t) = (oddHeat s).comp (oddHeat t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp only [oddHeat_coe, ContinuousLinearMap.comp_apply, heat_semigroup hs ht]

theorem oddHeat_contraction (t : ℝ) (f : oddSpace) : ‖oddHeat t f‖ ≤ ‖f‖ :=
  heat_contraction t f

end HeatCircleReflection
#check @HeatCircleReflection.fourierCoeff_reflect
#print axioms HeatCircleReflection.fourierCoeff_reflect
#check @HeatCircleReflection.reflect_heat
#print axioms HeatCircleReflection.reflect_heat
#check @HeatCircleReflection.heat_preserves_odd
#print axioms HeatCircleReflection.heat_preserves_odd

#check @HeatCircleReflection.oddSpace_closed
#print axioms HeatCircleReflection.oddSpace_closed
#check @HeatCircleReflection.oddHeat_zero
#print axioms HeatCircleReflection.oddHeat_zero
#check @HeatCircleReflection.oddHeat_semigroup
#print axioms HeatCircleReflection.oddHeat_semigroup
#check @HeatCircleReflection.oddHeat_contraction
#print axioms HeatCircleReflection.oddHeat_contraction
#check @HeatCircleReflection.mem_oddSpace
#print axioms HeatCircleReflection.mem_oddSpace
#check @HeatCircleReflection.odd_heat_invariant
#print axioms HeatCircleReflection.odd_heat_invariant
#check @HeatCircleReflection.oddHeat_coe
#print axioms HeatCircleReflection.oddHeat_coe
#check @HeatCircleReflection.reflect_ae
#print axioms HeatCircleReflection.reflect_ae
