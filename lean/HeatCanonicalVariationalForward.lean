import HeatVariationalForwardModel
import HeatCanonicalSeparable
import HeatCanonicalControlledContinuous

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatCanonicalVariationalForward
open MeasureTheory SHE SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
open HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
abbrev Control := Lp ℝ 2 paperControlMeasure
local instance : MeasurableSpace Control := borel Control
local instance : BorelSpace Control := ⟨rfl⟩
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener

theorem exists_solution (T : ℝ≥0) (hT : 0<T) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖≤1) (g : Base) :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∀ U : ℝ≥0 → C(ℝ≥0,ℝ) → Control,
      HeatFiniteControlExtension.LocallyProgressive F T U →
      Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖U p.1 p.2‖^2) (energyMeasure μ T) →
      let Uf := fun s ω => paperB (U (min s T) ω)
      ∃ I : StandardTerminalIto (C := Base) (E := Base) F μ T,
        ∃ hp : IsStronglyProgressive F Uf,
        ∃ hE : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Uf p.1 p.2‖^2) (energyMeasure μ T),
          Nonempty (HeatVariationalForwardModel.Solution F μ T (noise b hb hbound) I Uf hp hE g) := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : IsSeparable μ := HeatCanonicalSeparable.completed_separable
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  intro U hU hE
  obtain ⟨w,hw,⟨basis⟩⟩ := HeatCountableBasis.exists_countable_hilbertBasis (E := Base)
  letI : Countable w := hw.to_subtype
  let J := HeatCanonicalNative.scalar T
  let I := HeatTerminalNaturality.integral F μ T basis J
  let Ue := fun s ω => U (min s T) ω
  have hUe : IsStronglyProgressive F Ue := HeatFiniteControlExtension.extend F T U hU
  have heq := HeatFiniteControlExtension.energy_ae μ T U
  have hEe : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Ue p.1 p.2‖^2) (energyMeasure μ T) :=
    hE.congr (heq.fun_comp (fun y : Control => ‖y‖^2)).symm
  have hp : IsStronglyProgressive F (fun s ω => paperB (Ue s ω)) :=
    HeatControlInjection.progressive (E := Base) F paperB Ue hUe
  have henergy := HeatControlInjection.energy (E := Base) F μ T paperB Ue hUe hEe
  refine ⟨I,hp,henergy,?_⟩
  exact HeatVariationalForwardModel.exists_solution F μ T (noise b hb hbound) basis J hT
    (HeatCanonicalNative.locality T) (HeatCanonicalNative.continuous_stopped T)
    HeatCanonicalNullComplete.contains_nulls (SHEStochastic.NativeScalarBDG.constant 3)
    (HeatCanonicalBDG.hilbert_bdg basis T 3) (fun s ω => paperB (Ue s ω)) hp henergy g

end HeatCanonicalVariationalForward
#check @HeatCanonicalVariationalForward.exists_solution
#print HeatCanonicalVariationalForward.exists_solution
#print axioms HeatCanonicalVariationalForward.exists_solution
