import HeatOddEmbedding

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatOddSurjectivity
open MeasureTheory AddCircle HeatCircleIntervalCoordinates HeatFoldProbability HeatOddEmbedding
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def sectionPoint (y : ℝ) : AddCircle (1 : ℝ) := ((y / 20 : ℝ) : AddCircle (1 : ℝ))

theorem sectionPoint_measurable : Measurable sectionPoint := by
  exact AddCircle.measurable_mk'.comp (measurable_id.div_const 20)

theorem sectionPoint_position (x : AddCircle (1 : ℝ)) :
    sectionPoint (position x) = if 0 ≤ coordinate x then x else -x := by
  have hc : ((coordinate x : ℝ) : AddCircle (1 : ℝ)) = x := AddCircle.coe_equivIoc
  unfold sectionPoint position
  have hs : (20 * |coordinate x|) / 20 = |coordinate x| := by ring
  rw [hs]
  by_cases h : 0 ≤ coordinate x
  · simp only [h, ite_true, abs_of_nonneg h, hc]
  · have hh : coordinate x ≤ 0 := le_of_not_ge h
    simp only [h, ite_false, abs_of_nonpos hh]
    change -((coordinate x : ℝ) : AddCircle (1 : ℝ)) = -x
    rw [hc]

theorem orientation_neg_ae : ∀ᵐ x ∂circleMeasure, orientation (-x) = -orientation x := by
  filter_upwards [position_atoms_null 0, position_atoms_null 10] with x h0 h10
  have hθ0 : coordinate x ≠ 0 := by
    intro hh
    apply h0
    simp [position, hh]
  have hθseam : coordinate x ≠ 1/2 := by
    intro hh
    apply h10
    norm_num [position, hh]
  have hθ := coordinate_neg x hθseam
  unfold orientation
  rw [hθ]
  by_cases hle : 0 ≤ coordinate x
  · have hp : 0 < coordinate x := lt_of_le_of_ne hle (Ne.symm hθ0)
    have hn : ¬ 0 ≤ -coordinate x := by linarith
    simp [hle, hn]
  · have hn : 0 ≤ -coordinate x := by linarith
    simp [hle, hn]

theorem signed_odd_even (g : HeatRealOddSemigroup.oddSpace) :
    (fun x => signOperator g (-x)) =ᵐ[circleMeasure] (signOperator g : AddCircle (1 : ℝ) → ℝ) := by
  have ho : HeatRealOddSemigroup.reflection (g : CircleL2) = -(g : CircleL2) :=
    (HeatRealOddSemigroup.mem_oddSpace _).1 g.property
  have hsignneg := (Measure.measurePreserving_neg circleMeasure).quasiMeasurePreserving.ae (signOperator_ae (g : CircleL2))
  have hreflect := HeatRealOddSemigroup.reflection_ae (g : CircleL2)
  rw [ho] at hreflect
  filter_upwards [hsignneg, signOperator_ae (g : CircleL2), orientation_neg_ae,
    hreflect, Lp.coeFn_neg (g : CircleL2)] with x hsn hs hor href hneg
  have hval : (g : CircleL2) (-x) = -(g : CircleL2) x := by
    calc
      _ = (-(g : CircleL2)) x := href.symm
      _ = _ := by simpa only [Pi.neg_apply] using hneg
  rw [hsn, hs, hor, hval]
  ring


theorem intoOdd_surjective : Function.Surjective intoOdd := by
  intro g
  let h : CircleL2 := signOperator (g : CircleL2)
  let u : ℝ → ℝ := fun y => h (sectionPoint y)
  have hstrong : StronglyMeasurable u :=
    (Lp.stronglyMeasurable h).comp_measurable sectionPoint_measurable
  have heven := signed_odd_even g
  have hcomp : (fun x => u (position x)) =ᵐ[circleMeasure] h := by
    filter_upwards [heven] with x hx
    change h (sectionPoint (position x)) = h x
    rw [sectionPoint_position]
    split
    · rfl
    · exact hx
  have hm : MemLp u 2 normalizedIntervalMeasure := by
    rw [← position_measurePreserving.map_eq]
    apply (memLp_map_measure_iff hstrong.aestronglyMeasurable position_measurable.aemeasurable).2
    exact (Lp.memLp h).ae_eq hcomp.symm
  let f : Lp ℝ 2 normalizedIntervalMeasure := hm.toLp u
  have hf : (pullback f : CircleL2) = h := by
    apply Lp.ext
    have heq := position_measurePreserving.quasiMeasurePreserving.ae hm.coeFn_toLp
    filter_upwards [pullback_ae f, heq, hcomp] with x ha hb hc
    exact ha.trans (hb.trans hc)
  refine ⟨f, ?_⟩
  apply Subtype.ext
  change (intoOdd f : CircleL2) = (g : CircleL2)
  rw [intoOdd_coe]
  change signOperator (pullback f) = (g : CircleL2)
  rw [hf, show h = signOperator (g : CircleL2) from rfl, signOperator_twice]


/-- The proved odd extension is a surjective linear isometry. -/
def oddEquiv : Lp ℝ 2 normalizedIntervalMeasure ≃ₗᵢ[ℝ] HeatRealOddSemigroup.oddSpace :=
  LinearIsometryEquiv.ofSurjective intoOdd intoOdd_surjective

theorem oddEquiv_apply (f : Lp ℝ 2 normalizedIntervalMeasure) : oddEquiv f = intoOdd f := rfl

theorem oddEquiv_left_inverse (f : Lp ℝ 2 normalizedIntervalMeasure) :
    oddEquiv.symm (oddEquiv f) = f := oddEquiv.symm_apply_apply f

theorem oddEquiv_right_inverse (g : HeatRealOddSemigroup.oddSpace) :
    oddEquiv (oddEquiv.symm g) = g := oddEquiv.apply_symm_apply g

def transportedHeat (t : ℝ) :
    Lp ℝ 2 normalizedIntervalMeasure →L[ℝ] Lp ℝ 2 normalizedIntervalMeasure :=
  oddEquiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((HeatRealOddSemigroup.timeScaledHeat t).comp oddEquiv.toLinearIsometry.toContinuousLinearMap)

theorem transportedHeat_apply (t : ℝ) (f : Lp ℝ 2 normalizedIntervalMeasure) :
    transportedHeat t f = oddEquiv.symm (HeatRealOddSemigroup.timeScaledHeat t (oddEquiv f)) := rfl

theorem transportedHeat_zero :
    transportedHeat 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 normalizedIntervalMeasure) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [transportedHeat_apply, HeatRealOddSemigroup.timeScaledHeat_zero]
  simp

theorem transportedHeat_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    transportedHeat (s+t) = (transportedHeat s).comp (transportedHeat t) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, transportedHeat_apply,
    HeatRealOddSemigroup.timeScaledHeat_semigroup hs ht, oddEquiv.apply_symm_apply]

theorem transportedHeat_contraction (t : ℝ) (f : Lp ℝ 2 normalizedIntervalMeasure) :
    ‖transportedHeat t f‖ ≤ ‖f‖ := by
  rw [transportedHeat_apply, oddEquiv.symm.norm_map, ← oddEquiv.norm_map f]
  exact HeatRealOddSemigroup.timeScaledHeat_contraction t (oddEquiv f)

theorem transportedHeat_continuous (f : Lp ℝ 2 normalizedIntervalMeasure) :
    Continuous (fun t : ℝ => transportedHeat t f) := by
  have hc := HeatRealOddSemigroup.timeScaledHeat_continuous (oddEquiv f)
  change Continuous (fun t : ℝ => oddEquiv.symm (HeatRealOddSemigroup.timeScaledHeat t (oddEquiv f)))
  exact oddEquiv.symm.continuous.comp hc

end HeatOddSurjectivity
#check @HeatOddSurjectivity.sectionPoint_measurable
#print axioms HeatOddSurjectivity.sectionPoint_measurable
#check @HeatOddSurjectivity.sectionPoint_position
#print axioms HeatOddSurjectivity.sectionPoint_position
#check @HeatOddSurjectivity.orientation_neg_ae
#print axioms HeatOddSurjectivity.orientation_neg_ae
#check @HeatOddSurjectivity.signed_odd_even
#print axioms HeatOddSurjectivity.signed_odd_even

#check @HeatOddSurjectivity.intoOdd_surjective
#print axioms HeatOddSurjectivity.intoOdd_surjective

#check @HeatOddSurjectivity.oddEquiv_left_inverse
#print axioms HeatOddSurjectivity.oddEquiv_left_inverse
#check @HeatOddSurjectivity.oddEquiv_right_inverse
#print axioms HeatOddSurjectivity.oddEquiv_right_inverse
#check @HeatOddSurjectivity.transportedHeat_zero
#print axioms HeatOddSurjectivity.transportedHeat_zero
#check @HeatOddSurjectivity.transportedHeat_semigroup
#print axioms HeatOddSurjectivity.transportedHeat_semigroup
#check @HeatOddSurjectivity.transportedHeat_contraction
#print axioms HeatOddSurjectivity.transportedHeat_contraction
#check @HeatOddSurjectivity.transportedHeat_continuous
#print axioms HeatOddSurjectivity.transportedHeat_continuous
#check @HeatOddSurjectivity.oddEquiv_apply
#print axioms HeatOddSurjectivity.oddEquiv_apply
#check @HeatOddSurjectivity.transportedHeat_apply
#print axioms HeatOddSurjectivity.transportedHeat_apply
