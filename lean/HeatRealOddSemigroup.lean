import HeatCircleReflection

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatRealOddSemigroup
open SHE MeasureTheory AddCircle CircleHeat DyadicApproximation FiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def reflection : RealL2 →L[ℝ] RealL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : AddCircle (1 : ℝ) => -x)
    (Measure.measurePreserving_neg haarAddCircle)).toContinuousLinearMap

theorem reflection_ae (f : RealL2) : reflection f =ᵐ[haarAddCircle] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem realEmbed_reflection (f : RealL2) :
    realEmbed (reflection f) = HeatCircleReflection.reflect (realEmbed f) := by
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg (haarAddCircle (T := (1 : ℝ)))).quasiMeasurePreserving.ae (realEmbed_ae f)
  filter_upwards [realEmbed_ae (reflection f), reflection_ae f,
    HeatCircleReflection.reflect_ae (realEmbed f), hneg] with x h1 h2 h3 h4
  rw [h1,h2,h3]
  exact h4.symm

theorem reflection_heat (t : ℝ) (f : RealL2) :
    reflection (RealHeat.realHeat t f) = RealHeat.realHeat t (reflection f) := by
  apply realCircleIdentification.injective
  apply Subtype.ext
  change realEmbed (reflection (RealHeat.realHeat t f)) = realEmbed (RealHeat.realHeat t (reflection f))
  rw [realEmbed_reflection, RealHeat.realEmbed_realHeat,
    RealHeat.realEmbed_realHeat, realEmbed_reflection, HeatCircleReflection.reflect_heat]

def oddSpace : Submodule ℝ RealL2 :=
  (reflection + ContinuousLinearMap.id ℝ RealL2).toLinearMap.ker

theorem mem_oddSpace (f : RealL2) : f ∈ oddSpace ↔ reflection f = -f := by
  change reflection f + f = 0 ↔ reflection f = -f
  exact add_eq_zero_iff_eq_neg

theorem oddSpace_closed : IsClosed (oddSpace : Set RealL2) :=
  (reflection + ContinuousLinearMap.id ℝ RealL2).isClosed_ker

theorem odd_heat_invariant (t : ℝ) (f : RealL2) (hf : f ∈ oddSpace) :
    RealHeat.realHeat t f ∈ oddSpace := by
  apply (mem_oddSpace _).2
  rw [reflection_heat, (mem_oddSpace _).1 hf, map_neg]

def oddHeat (t : ℝ) : oddSpace →L[ℝ] oddSpace :=
  ((RealHeat.realHeat t).domRestrict oddSpace).codRestrict oddSpace
    (fun f => odd_heat_invariant t f f.property)

theorem oddHeat_coe (t : ℝ) (f : oddSpace) : (oddHeat t f : RealL2) = RealHeat.realHeat t f := rfl

theorem oddHeat_zero : oddHeat 0 = ContinuousLinearMap.id ℝ oddSpace := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp [oddHeat_coe, RealHeat.realHeat_zero]

theorem oddHeat_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    oddHeat (s+t) = (oddHeat s).comp (oddHeat t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp only [oddHeat_coe, ContinuousLinearMap.comp_apply, RealHeat.realHeat_semigroup hs ht]

theorem oddHeat_contraction (t : ℝ) (f : oddSpace) : ‖oddHeat t f‖ ≤ ‖f‖ :=
  RealHeat.realHeat_contraction t f

theorem oddHeat_continuous (f : oddSpace) : Continuous (fun t : ℝ => oddHeat t f) := by
  apply continuous_induced_rng.mpr
  have hp : Continuous (fun t : ℝ => (t, (f : RealL2))) := continuous_id.prodMk continuous_const
  have ha : Continuous ((fun p : ℝ × RealL2 => RealHeat.realHeat p.1 p.2) ∘
      (fun t : ℝ => (t, (f : RealL2)))) := Continuous.comp RealHeat.continuous_realHeat_action hp
  simpa only [Function.comp_def, oddHeat_coe] using ha


/-- Rescale the unit circle clock for the length-ten half period. The
identification of this odd subspace with L2(0,10) is a separate obligation. -/
def timeScaledHeat (t : ℝ) : oddSpace →L[ℝ] oddSpace := oddHeat (t / 400)

theorem timeScaledHeat_zero : timeScaledHeat 0 = ContinuousLinearMap.id ℝ oddSpace := by
  simpa [timeScaledHeat] using oddHeat_zero

theorem timeScaledHeat_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    timeScaledHeat (s+t) = (timeScaledHeat s).comp (timeScaledHeat t) := by
  unfold timeScaledHeat
  rw [add_div]
  exact oddHeat_semigroup (div_nonneg hs (by norm_num)) (div_nonneg ht (by norm_num))

theorem timeScaledHeat_contraction (t : ℝ) (f : oddSpace) : ‖timeScaledHeat t f‖ ≤ ‖f‖ :=
  oddHeat_contraction (t / 400) f

theorem timeScaledHeat_continuous (f : oddSpace) : Continuous (fun t : ℝ => timeScaledHeat t f) :=
  (oddHeat_continuous f).comp (continuous_id.div_const 400)

end HeatRealOddSemigroup
#check @HeatRealOddSemigroup.realEmbed_reflection
#print axioms HeatRealOddSemigroup.realEmbed_reflection
#check @HeatRealOddSemigroup.reflection_heat
#print axioms HeatRealOddSemigroup.reflection_heat
#check @HeatRealOddSemigroup.mem_oddSpace
#print axioms HeatRealOddSemigroup.mem_oddSpace
#check @HeatRealOddSemigroup.oddSpace_closed
#print axioms HeatRealOddSemigroup.oddSpace_closed
#check @HeatRealOddSemigroup.odd_heat_invariant
#print axioms HeatRealOddSemigroup.odd_heat_invariant
#check @HeatRealOddSemigroup.oddHeat_coe
#print axioms HeatRealOddSemigroup.oddHeat_coe
#check @HeatRealOddSemigroup.oddHeat_zero
#print axioms HeatRealOddSemigroup.oddHeat_zero
#check @HeatRealOddSemigroup.oddHeat_semigroup
#print axioms HeatRealOddSemigroup.oddHeat_semigroup
#check @HeatRealOddSemigroup.oddHeat_contraction
#print axioms HeatRealOddSemigroup.oddHeat_contraction
#check @HeatRealOddSemigroup.oddHeat_continuous
#print axioms HeatRealOddSemigroup.oddHeat_continuous

#check @HeatRealOddSemigroup.timeScaledHeat_zero
#print axioms HeatRealOddSemigroup.timeScaledHeat_zero
#check @HeatRealOddSemigroup.timeScaledHeat_semigroup
#print axioms HeatRealOddSemigroup.timeScaledHeat_semigroup
#check @HeatRealOddSemigroup.timeScaledHeat_contraction
#print axioms HeatRealOddSemigroup.timeScaledHeat_contraction
#check @HeatRealOddSemigroup.timeScaledHeat_continuous
#print axioms HeatRealOddSemigroup.timeScaledHeat_continuous
#check @HeatRealOddSemigroup.reflection_ae
#print axioms HeatRealOddSemigroup.reflection_ae
