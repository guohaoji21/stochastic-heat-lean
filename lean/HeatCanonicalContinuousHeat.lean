import HeatContinuousMild
import HeatContinuousMoments
import HeatCanonicalBDG
import HeatCanonicalNullComplete
import HeatPaperSmoothing
import HeatPaperCovariance

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatCanonicalContinuousHeat
open MeasureTheory SHE SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
open HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate

theorem exists_solution (T : ℝ≥0) (hT : 0<T) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖≤1) (g : Base) :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∃ I : StandardTerminalIto (C := Base) (E := Base) F μ T,
      ∃ u : Process (E := Base) F μ T,
        u=HeatVolterraForcing.orbit F μ T family family_continuous family_contraction g+
          HeatVolterraFixedPoint.convolution F μ T family family_continuous family_contraction
            (noise b hb hbound) family_semigroup I u ∧
        ∃ Y : ℝ≥0 → C(ℝ≥0,ℝ) → Base,
          (∀ ω, Continuous (fun t => Y t ω)) ∧ StronglyAdapted F Y ∧
          StronglyMeasurable[(F).predictable] (Function.uncurry Y) ∧
          (Y 0=ᵐ[μ] (fun _ => g)) ∧
          (u=ᵐ[energyMeasure μ T] Function.uncurry Y) ∧
          Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Y p.1 p.2‖^2) (energyMeasure μ T) ∧
          (∀ t, t≤T → Y t=ᵐ[μ] HeatMildSolution.value F μ T family family_continuous family_contraction
            (noise b hb hbound) I g u t) ∧
          (∀ a c : ℝ≥0, a≤c → c≤T →
            μ[Y c | F a]=ᵐ[μ] (fun ω => family (c-a) (Y a ω)) ∧
            μ[(fun ω => (W c ω-W a ω) • Y c ω) | F a]=ᵐ[μ]
              (fun ω => ((c:ℝ)-(a:ℝ)) • HeatPaperCovariance.K b hb hbound (c-a) (Y a ω))) := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  obtain ⟨w,hw,⟨basis⟩⟩ := HeatCountableBasis.exists_countable_hilbertBasis (E := Base)
  letI : Countable w := hw.to_subtype
  let J := HeatCanonicalNative.scalar T
  let I := HeatTerminalNaturality.integral F μ T basis J
  have hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : Base,
      ‖family δ (family τ x)-family τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖ := by
    intro τ δ hτ x
    exact HeatPaperSmoothing.paper_bound (by exact_mod_cast hτ) δ.property (by norm_num) (by norm_num) x
  have hBDG : StandardTerminalBDGPower 8 I (SHEStochastic.NativeScalarBDG.constant 3) :=
    HeatCanonicalBDG.hilbert_bdg basis T 3
  obtain ⟨u,hu,Y,hYc,hYa,hYp,hY0,hueq,hEn,hrep⟩ :=
    HeatContinuousMild.exists_solution F μ T family family_continuous family_contraction (noise b hb hbound)
      family_semigroup hsmooth I hT HeatCanonicalNullComplete.contains_nulls paperHeat_zero _ hBDG g
  refine ⟨I,u,hu,Y,hYc,hYa,hYp,hY0,hueq,hEn,hrep,?_⟩
  intro a c hac hcT
  exact HeatContinuousMoments.moments F μ T family family_continuous family_contraction (noise b hb hbound)
    family_semigroup basis J (HeatCanonicalNative.locality T) W (HeatCanonicalNative.coordinate T) g u hu Y hrep hac hcT

end HeatCanonicalContinuousHeat
#check @HeatCanonicalContinuousHeat.exists_solution
#print HeatCanonicalContinuousHeat.exists_solution
#print axioms HeatCanonicalContinuousHeat.exists_solution
