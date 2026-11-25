import HeatControlledMild
import HeatControlInjection
import HeatCanonicalContinuousHeat
import HeatRestrictionAdjoint
import HeatBaseNontrivial

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatCanonicalControlledHeat
open MeasureTheory SHE SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
open HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : Nontrivial Base := HeatBaseNontrivial.nontrivial
abbrev Control := Lp ℝ 2 paperControlMeasure
local instance : MeasurableSpace Control := borel Control
local instance : BorelSpace Control := ⟨rfl⟩
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener

theorem exists_solution (T : ℝ≥0) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖≤1) (g : Base) :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∀ U : ℝ≥0 → C(ℝ≥0,ℝ) → Control, IsStronglyProgressive F U →
      Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖U p.1 p.2‖^2) (energyMeasure μ T) →
      ∃ I : StandardTerminalIto (C := Base) (E := Base) F μ T,
        ∃ A u : Process (E := Base) F μ T, ∃ V : ℝ≥0 → Lp Base 2 μ,
          u=HeatVolterraForcing.orbit F μ T family family_continuous family_contraction g+A+
            HeatVolterraFixedPoint.convolution F μ T family family_continuous family_contraction
              (noise b hb hbound) family_semigroup I u ∧
          Continuous V ∧ V 0=Lp.const 2 μ g ∧
          (∀ s, ∃ Z, StronglyMeasurable[F s] Z ∧ V s=ᵐ[μ] Z) ∧
          (∀ᵐ s ∂timeMeasure T, (fun ω => u (s,ω))=ᵐ[μ] V s) ∧
          (∀ s, V s=ᵐ[μ] fun ω => family s g+
            HeatControlConvolution.value T family
              (HeatControlAdapted.clamp (fun r ω => paperB (U r ω)) T) s ω+
            I.integral (HeatVolterraSlice.slice F μ T family family_continuous family_contraction
              (noise b hb hbound) s u) ω) := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  intro U hU hE
  obtain ⟨w,hw,⟨basis⟩⟩ := HeatCountableBasis.exists_countable_hilbertBasis (E := Base)
  letI : Countable w := hw.to_subtype
  let J := HeatCanonicalNative.scalar T
  let I := HeatTerminalNaturality.integral F μ T basis J
  have hp : IsStronglyProgressive F (fun s ω => paperB (U s ω)) :=
    HeatControlInjection.progressive (E := Base) F paperB U hU
  have henergy : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖paperB (U p.1 p.2)‖^2) (energyMeasure μ T) :=
    HeatControlInjection.energy (E := Base) F μ T paperB U hU hE
  obtain ⟨A,u,V,hu,hc,h0,ha,hs,hr⟩ := HeatControlledMild.exists_solution F μ T family
    family_continuous family_contraction (noise b hb hbound) family_semigroup I paperHeat_zero
    HeatCanonicalNullComplete.contains_nulls (fun s ω => paperB (U s ω)) hp henergy g
  exact ⟨I,A,u,V,hu,hc,h0,ha,hs,hr⟩

end HeatCanonicalControlledHeat
#check @HeatCanonicalControlledHeat.exists_solution
#print HeatCanonicalControlledHeat.exists_solution
#print axioms HeatCanonicalControlledHeat.exists_solution
