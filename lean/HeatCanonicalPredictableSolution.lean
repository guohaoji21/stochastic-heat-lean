import HeatCanonicalTerminal
import HeatVolterraFixedPoint
import HeatVolterraForcing
import HeatDirichletIdentification
import HeatScalarMultiplier

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatCanonicalPredictableSolution
open MeasureTheory SHE SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
open scoped NNReal ENNReal

local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure; infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener

def noise (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) : Base →L[ℝ] Base :=
  SHEStochastic.BoundedFieldOperator.operator (HeatScalarMultiplier.field baseMeasure b hb hbound)

theorem family_semigroup (s t : ℝ≥0) : family (s+t) = (family s).comp (family t) := by
  change paperHeat ((s:ℝ)+(t:ℝ)) = (paperHeat s).comp (paperHeat t)
  exact paperHeat_semigroup s.property t.property

theorem canonical_predictable_solution (T : ℝ≥0) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (g : Base) :
    letI : MeasurableSpace C(ℝ≥0, ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∃ I : StandardTerminalIto (C := Base) (E := Base) F μ T,
      ∃! Y : Process (E := Base) F μ T,
        Y = HeatVolterraForcing.orbit F μ T family family_continuous family_contraction g +
          HeatVolterraFixedPoint.convolution F μ T family family_continuous family_contraction
            (noise b hb hbound) family_semigroup I Y := by
  letI : MeasurableSpace C(ℝ≥0, ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  obtain ⟨I⟩ := HeatCanonicalTerminal.canonical_terminal_nonempty (E := Base) T
  exact ⟨I, HeatVolterraFixedPoint.exists_unique F μ T family family_continuous family_contraction
    (noise b hb hbound) family_semigroup I (HeatVolterraForcing.orbit F μ T family family_continuous family_contraction g)⟩

end HeatCanonicalPredictableSolution
#check @HeatCanonicalPredictableSolution.family_semigroup
#print axioms HeatCanonicalPredictableSolution.family_semigroup
#check @HeatCanonicalPredictableSolution.canonical_predictable_solution
#print axioms HeatCanonicalPredictableSolution.canonical_predictable_solution
