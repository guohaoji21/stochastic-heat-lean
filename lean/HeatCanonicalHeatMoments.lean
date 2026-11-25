import HeatCanonicalPredictableSolution
import HeatMildSecondMoment

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatCanonicalHeatMoments
open MeasureTheory SHE SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
open HeatCanonicalPredictableSolution HeatMildSolution
open scoped NNReal ENNReal

local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure; infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate

theorem canonical_mild_and_moments (T : ℝ≥0) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1) (g : Base) :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∃ I : StandardTerminalIto (C := Base) (E := Base) F μ T,
      ∃ u : Process (E := Base) F μ T,
        u = HeatVolterraForcing.orbit F μ T family family_continuous family_contraction g +
          HeatVolterraFixedPoint.convolution F μ T family family_continuous family_contraction
            (noise b hb hbound) family_semigroup I u ∧
        Continuous (value F μ T family family_continuous family_contraction (noise b hb hbound) I g u) ∧
        (∀ t, ∃ Z : C(ℝ≥0,ℝ) → Base, StronglyMeasurable[F t] Z ∧
          value F μ T family family_continuous family_contraction (noise b hb hbound) I g u t =ᵐ[μ] Z) ∧
        (∀ᵐ t ∂timeMeasure T, (fun ω => u (t,ω)) =ᵐ[μ]
          value F μ T family family_continuous family_contraction (noise b hb hbound) I g u t) ∧
        value F μ T family family_continuous family_contraction (noise b hb hbound) I g u 0 = Lp.const 2 μ g ∧
        (∀ a c : ℝ≥0, a ≤ c → c ≤ T →
          μ[(value F μ T family family_continuous family_contraction (noise b hb hbound) I g u c : C(ℝ≥0,ℝ) → Base) | F a] =ᵐ[μ]
            (fun ω => family (c-a) (value F μ T family family_continuous family_contraction (noise b hb hbound) I g u a ω)) ∧
          μ[(fun ω => (W c ω-W a ω) • value F μ T family family_continuous family_contraction (noise b hb hbound) I g u c ω) | F a] =ᵐ[μ]
            (fun ω => ((c:ℝ)-(a:ℝ)) • ∫ v in (0:ℝ)..1,
              HeatIntervalCovariance.extend family ((1-v)*((c:ℝ)-(a:ℝ)))
                ((noise b hb hbound) (HeatIntervalCovariance.extend family (v*((c:ℝ)-(a:ℝ)))
                  (value F μ T family family_continuous family_contraction (noise b hb hbound) I g u a ω))))) := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  obtain ⟨w,hw,⟨basis⟩⟩ := HeatCountableBasis.exists_countable_hilbertBasis (E := Base)
  letI : Countable w := hw.to_subtype
  obtain ⟨J,hlocal,hW,_⟩ := HeatCanonicalUsualCross56.canonical_interval_cross T basis HeatTerminalBrownian.e
  let I := HeatTerminalNaturality.integral F μ T basis J
  obtain ⟨u,hu,hunique⟩ := HeatVolterraFixedPoint.exists_unique F μ T family family_continuous family_contraction
    (noise b hb hbound) family_semigroup I (HeatVolterraForcing.orbit F μ T family family_continuous family_contraction g)
  refine ⟨I,u,hu,value_continuous F μ T family family_continuous family_contraction (noise b hb hbound) I g u,
    value_adapted F μ T family family_continuous family_contraction (noise b hb hbound) I g u,
    value_slices F μ T family family_continuous family_contraction (noise b hb hbound) I family_semigroup g u hu,
    initial_value F μ T family family_continuous family_contraction (noise b hb hbound) I paperHeat_zero g u,?_⟩
  intro a c hac hcT
  refine ⟨HeatMildRestart.conditional_mean F μ T family family_continuous family_contraction
    (noise b hb hbound) family_semigroup basis J hlocal hac g u, ?_⟩
  have hs := HeatMildSecondMoment.second_moment F μ T family family_continuous family_contraction
    (noise b hb hbound) family_semigroup basis J hlocal hac hcT g u hu
  have he : (fun ω => (W c ω-W a ω) • value F μ T family family_continuous family_contraction (noise b hb hbound) I g u c ω) =ᵐ[μ]
      (fun ω => (J.integral (StoppedItoInputs.stop F μ T c
        (RawCylindricalCoordinates.row F μ T (HeatTerminalBrownian.e : Unit → SHE.HilbertColumns.Space Unit ℝ) ())) ω -
        J.integral (StoppedItoInputs.stop F μ T a
        (RawCylindricalCoordinates.row F μ T (HeatTerminalBrownian.e : Unit → SHE.HilbertColumns.Space Unit ℝ) ())) ω) •
        value F μ T family family_continuous family_contraction (noise b hb hbound) I g u c ω) := by
    filter_upwards [hW c hcT,hW a (hac.trans hcT)] with ω hc ha
    rw [hc,ha]
  exact (condExp_congr_ae (m := F a) he).trans hs

end HeatCanonicalHeatMoments
#check @HeatCanonicalHeatMoments.canonical_mild_and_moments
#print HeatCanonicalHeatMoments.canonical_mild_and_moments
#print axioms HeatCanonicalHeatMoments.canonical_mild_and_moments
