import HeatControlledContinuous
import HeatCanonicalControlledHeat
import HeatFiniteControlExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatCanonicalControlledContinuous
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

theorem exists_solution (T : ℝ≥0) (hT : 0<T) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖≤1) (g : Base) :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∀ U : ℝ≥0 → C(ℝ≥0,ℝ) → Control,
      HeatFiniteControlExtension.LocallyProgressive F T U →
      Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖U p.1 p.2‖^2) (energyMeasure μ T) →
      ∃ I : StandardTerminalIto (C := Base) (E := Base) F μ T,
        ∃ A u : Process (E := Base) F μ T,
          u=HeatVolterraForcing.orbit F μ T family family_continuous family_contraction g+A+
            HeatVolterraFixedPoint.convolution F μ T family family_continuous family_contraction
              (noise b hb hbound) family_semigroup I u ∧
          ∃ Y : ℝ≥0 → C(ℝ≥0,ℝ) → Base,
            (∀ ω, Continuous (fun s => Y s ω)) ∧ StronglyAdapted F Y ∧
            StronglyMeasurable[(F).predictable] (Function.uncurry Y) ∧
            (Y 0=ᵐ[μ] fun _ => g) ∧ u=ᵐ[energyMeasure μ T] Function.uncurry Y ∧
            Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Y p.1 p.2‖^2) (energyMeasure μ T) ∧
            (∀ s, s≤T → Y s=ᵐ[μ] fun ω => family s g+
              HeatControlConvolution.value T family
                (HeatControlAdapted.clamp (fun r ω => paperB (U (min r T) ω)) T) s ω+
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
  let Ue := fun s ω => U (min s T) ω
  have hUe : IsStronglyProgressive F Ue := HeatFiniteControlExtension.extend F T U hU
  have heq := HeatFiniteControlExtension.energy_ae μ T U
  have hEe : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Ue p.1 p.2‖^2) (energyMeasure μ T) :=
    hE.congr (heq.fun_comp (fun y : Control => ‖y‖^2)).symm
  have hp : IsStronglyProgressive F (fun s ω => paperB (Ue s ω)) :=
    HeatControlInjection.progressive (E := Base) F paperB Ue hUe
  have henergy := HeatControlInjection.energy (E := Base) F μ T paperB Ue hUe hEe
  have hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : Base,
      ‖family δ (family τ x)-family τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖ := by
    intro τ δ hτ x
    exact HeatPaperSmoothing.paper_bound (by exact_mod_cast hτ) δ.property (by norm_num) (by norm_num) x
  obtain ⟨A,u,hu,Y,hYc,hYa,hYp,hY0,hueq,hEn,hrep⟩ :=
    HeatControlledContinuous.exists_solution F μ T family family_continuous family_contraction
      (noise b hb hbound) family_semigroup hsmooth basis J hT paperHeat_zero
      (HeatCanonicalNative.locality T) (HeatCanonicalNative.continuous_stopped T)
      HeatCanonicalNullComplete.contains_nulls (SHEStochastic.NativeScalarBDG.constant 3)
      (HeatCanonicalBDG.hilbert_bdg basis T 3) (fun s ω => paperB (Ue s ω)) hp henergy g
  exact ⟨I,A,u,hu,Y,hYc,hYa,hYp,hY0,hueq,hEn,hrep⟩

end HeatCanonicalControlledContinuous
#check @HeatCanonicalControlledContinuous.exists_solution
#print HeatCanonicalControlledContinuous.exists_solution
#print axioms HeatCanonicalControlledContinuous.exists_solution
