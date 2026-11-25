import HeatFoldProbability
import HeatScalarMultiplier

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatOddEmbedding
open MeasureTheory AddCircle HeatCircleIntervalCoordinates HeatFoldProbability
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev circleMeasure : Measure (AddCircle (1 : ℝ)) := haarAddCircle
abbrev CircleL2 := Lp ℝ 2 circleMeasure

def orientation (x : AddCircle (1 : ℝ)) : ℝ := if 0 ≤ coordinate x then 1 else -1

theorem orientation_measurable : Measurable orientation := by
  unfold orientation
  exact Measurable.ite (measurableSet_le measurable_const coordinate_measurePreserving.measurable)
    measurable_const measurable_const

theorem orientation_square (x : AddCircle (1 : ℝ)) : orientation x * orientation x = 1 := by
  unfold orientation
  split <;> norm_num

theorem orientation_bound : ∀ᵐ x ∂circleMeasure, ‖orientation x‖ ≤ 1 := by
  filter_upwards [] with x
  unfold orientation
  split <;> norm_num

def signField : SHEStochastic.BoundedFieldOperator.Field circleMeasure ℝ ℝ :=
  HeatScalarMultiplier.field circleMeasure orientation orientation_measurable.aestronglyMeasurable orientation_bound

def signOperator : CircleL2 →L[ℝ] CircleL2 := SHEStochastic.BoundedFieldOperator.operator signField

theorem signOperator_ae (f : CircleL2) :
    (signOperator f : AddCircle (1 : ℝ) → ℝ) =ᵐ[circleMeasure] fun x => orientation x * f x := by
  have h := SHEStochastic.BoundedFieldOperator.operator_ae signField f
  exact h

theorem signOperator_twice (f : CircleL2) : signOperator (signOperator f) = f := by
  apply Lp.ext
  filter_upwards [signOperator_ae (signOperator f), signOperator_ae f] with x h1 h2
  rw [h1,h2,← mul_assoc,orientation_square,one_mul]

theorem signOperator_le (f : CircleL2) : ‖signOperator f‖ ≤ ‖f‖ := by
  have hm : ‖signOperator‖ ≤ 1 := SHEStochastic.BoundedFieldOperator.operator_norm signField
  exact (signOperator.le_opNorm f).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (norm_nonneg f))

theorem signOperator_norm (f : CircleL2) : ‖signOperator f‖ = ‖f‖ := by
  apply le_antisymm (signOperator_le f)
  have h := signOperator_le (signOperator f)
  rw [signOperator_twice] at h
  exact h

def signIsometry : CircleL2 →ₗᵢ[ℝ] CircleL2 where
  toLinearMap := signOperator.toLinearMap
  norm_map' := signOperator_norm

def embedding : Lp ℝ 2 normalizedIntervalMeasure →ₗᵢ[ℝ] CircleL2 :=
  signIsometry.comp pullback

theorem embedding_norm (f : Lp ℝ 2 normalizedIntervalMeasure) : ‖embedding f‖ = ‖f‖ :=
  embedding.norm_map f

theorem embedding_ae (f : Lp ℝ 2 normalizedIntervalMeasure) :
    (embedding f : AddCircle (1 : ℝ) → ℝ) =ᵐ[circleMeasure]
      fun x => orientation x * f (position x) := by
  filter_upwards [signOperator_ae (pullback f),pullback_ae f] with x hs hf
  exact hs.trans (congrArg (fun z => orientation x * z) hf)


/-- Reflection changes the centered coordinate away from the unique seam. -/
theorem coordinate_neg (x : AddCircle (1 : ℝ)) (hx : coordinate x ≠ 1/2) :
    coordinate (-x) = -coordinate x := by
  have hr := coordinate_mem x
  have hlt : coordinate x < 1/2 := lt_of_le_of_ne hr.2 hx
  have hb : -coordinate x ∈ Set.Ioc (-(1 : ℝ)/2) (-(1 : ℝ)/2 + 1) := by
    simp only [Set.mem_Ioc]
    constructor <;> linarith [hr.1, hlt]
  have heq : ((-coordinate x : ℝ) : AddCircle (1 : ℝ)) = -x := by
    change -((coordinate x : ℝ) : AddCircle (1 : ℝ)) = -x
    congr 1
    exact AddCircle.coe_equivIoc
  unfold coordinate
  rw [← heq]
  exact AddCircle.equivIoc_coe_of_mem hb

theorem position_atoms_null (a : ℝ) :
    ∀ᵐ x ∂circleMeasure, position x ≠ a := by
  have h : circleMeasure (position ⁻¹' {a}) = 0 := by
    rw [← Measure.map_apply position_measurable (measurableSet_singleton a), position_distribution]
    simp
  change circleMeasure {x | position x = a} = 0 at h
  exact (ae_iff).2 (by simpa only [not_not] using h)


theorem embedding_odd (f : Lp ℝ 2 normalizedIntervalMeasure) :
    embedding f ∈ HeatRealOddSemigroup.oddSpace := by
  apply (HeatRealOddSemigroup.mem_oddSpace _).2
  apply Lp.ext
  have hn := (Measure.measurePreserving_neg circleMeasure).quasiMeasurePreserving.ae (embedding_ae f)
  filter_upwards [position_atoms_null 0, position_atoms_null 10, embedding_ae f, hn,
    HeatRealOddSemigroup.reflection_ae (embedding f), Lp.coeFn_neg (embedding f)]
    with x h0 h10 he hen hr hneg
  have hθ0 : coordinate x ≠ 0 := by
    intro hh
    apply h0
    simp [position, hh]
  have hθseam : coordinate x ≠ 1/2 := by
    intro hh
    apply h10
    norm_num [position, hh]
  have hθ := coordinate_neg x hθseam
  have hp : position (-x) = position x := by simp [position, hθ]
  have ho : orientation (-x) = -orientation x := by
    unfold orientation
    rw [hθ]
    by_cases hle : 0 ≤ coordinate x
    · have hpositive : 0 < coordinate x := lt_of_le_of_ne hle (Ne.symm hθ0)
      have hneg : ¬ 0 ≤ -coordinate x := by linarith
      simp [hle, hneg]
    · have hneg : 0 ≤ -coordinate x := by linarith
      simp [hle, hneg]
  rw [hr, hen, hneg]
  simp only [Pi.neg_apply]
  rw [he, hp, ho]
  ring


def intoOdd : Lp ℝ 2 normalizedIntervalMeasure →ₗᵢ[ℝ] HeatRealOddSemigroup.oddSpace where
  toLinearMap := embedding.toLinearMap.codRestrict HeatRealOddSemigroup.oddSpace embedding_odd
  norm_map' := embedding_norm

theorem intoOdd_coe (f : Lp ℝ 2 normalizedIntervalMeasure) :
    (intoOdd f : CircleL2) = embedding f := rfl

theorem intoOdd_norm (f : Lp ℝ 2 normalizedIntervalMeasure) : ‖intoOdd f‖ = ‖f‖ :=
  intoOdd.norm_map f

theorem intoOdd_injective : Function.Injective intoOdd := intoOdd.injective

end HeatOddEmbedding
#check @HeatOddEmbedding.orientation_measurable
#print axioms HeatOddEmbedding.orientation_measurable
#check @HeatOddEmbedding.orientation_square
#print axioms HeatOddEmbedding.orientation_square
#check @HeatOddEmbedding.signOperator_ae
#print axioms HeatOddEmbedding.signOperator_ae
#check @HeatOddEmbedding.signOperator_twice
#print axioms HeatOddEmbedding.signOperator_twice
#check @HeatOddEmbedding.signOperator_le
#print axioms HeatOddEmbedding.signOperator_le
#check @HeatOddEmbedding.signOperator_norm
#print axioms HeatOddEmbedding.signOperator_norm
#check @HeatOddEmbedding.embedding_norm
#print axioms HeatOddEmbedding.embedding_norm
#check @HeatOddEmbedding.embedding_ae
#print axioms HeatOddEmbedding.embedding_ae

#check @HeatOddEmbedding.coordinate_neg
#print axioms HeatOddEmbedding.coordinate_neg
#check @HeatOddEmbedding.position_atoms_null
#print axioms HeatOddEmbedding.position_atoms_null
#check @HeatOddEmbedding.orientation_bound
#print axioms HeatOddEmbedding.orientation_bound

#check @HeatOddEmbedding.embedding_odd
#print axioms HeatOddEmbedding.embedding_odd

#check @HeatOddEmbedding.intoOdd_coe
#print axioms HeatOddEmbedding.intoOdd_coe
#check @HeatOddEmbedding.intoOdd_norm
#print axioms HeatOddEmbedding.intoOdd_norm
#check @HeatOddEmbedding.intoOdd_injective
#print axioms HeatOddEmbedding.intoOdd_injective
