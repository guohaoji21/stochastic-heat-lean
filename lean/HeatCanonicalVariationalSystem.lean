import HeatVariationalSystem
import HeatCanonicalVariationalForward
import HeatBackwardEndpointPairing
import HeatPaperCovariance
import HeatCanonicalControlledHeat
import HeatFiniteControlExtension
import HeatControlAdjointPairing
import HeatMultiplierAdjoint
import HeatPaperAdjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 3000000
noncomputable section
namespace HeatCanonicalVariationalSystem
open MeasureTheory Filter SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
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
local notation "W" => HeatCanonicalWiener56.coordinate

theorem exists_solution_and_duality (T : ℝ≥0) (hT : 0<T) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖≤1)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1≤N)
    (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=T) (g₀ g : Base) :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∀ U : ℝ≥0 → C(ℝ≥0,ℝ) → Control, HeatFiniteControlExtension.LocallyProgressive F T U →
      Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖U p.1 p.2‖^2) (energyMeasure μ T) →
      let Uf := fun s ω => paperB (U (min s T) ω)
      ∃ I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ T,
        ∃ hp : IsStronglyProgressive F Uf,
        ∃ hEn : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Uf p.1 p.2‖^2) (energyMeasure μ T),
        ∃ sol : HeatVariationalForwardModel.Solution F μ T (noise b hb hbound) I Uf hp hEn g₀,
        ∃ back : HeatBackwardModel.Solution F μ T (noise b hb hbound) I W t N g,
          (∫ ω,HeatBrownianProducts.products W t N ω*inner ℝ g (sol.weak.path T ω) ∂μ)=
            inner ℝ (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound)
              (fun k => t k-t (k-1)) N g 0) g₀+
            (∫ p,inner ℝ (U p.1 p.2) (paperBstar
              (HeatBackwardProcess.state family family_continuous family_contraction (noise b hb hbound) T W t N g p.1 p.2))
              ∂energyMeasure μ T) := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : IsSeparable μ := HeatCanonicalSeparable.completed_separable
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  intro U hU hE
  let z := HeatBackwardProcess.state family family_continuous family_contraction (noise b hb hbound) T W t N g
  obtain ⟨w,hw,⟨basis⟩⟩ := HeatCountableBasis.exists_countable_hilbertBasis (E := Base)
  letI : Countable w := hw.to_subtype
  let J := HeatCanonicalNative.scalar T
  let I := HeatTerminalNaturality.integral F μ T basis J
  let Ue := fun s ω => U (min s T) ω
  have hUe : IsStronglyProgressive F Ue := HeatFiniteControlExtension.extend F T U hU
  have heq := HeatFiniteControlExtension.energy_ae μ T U
  have hEe : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Ue p.1 p.2‖^2) (energyMeasure μ T) :=
    hE.congr (heq.fun_comp (fun y : Control => ‖y‖^2)).symm
  have hBU : IsStronglyProgressive F (fun s ω => paperB (Ue s ω)) :=
    HeatControlInjection.progressive (E := Base) F paperB Ue hUe
  have hBE := HeatControlInjection.energy (E := Base) F μ T paperB Ue hUe hEe
  have hWa : ∀ a, StronglyMeasurable[F a] (W a) := HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted
  have hP := HeatBrownianProducts.products_properties F μ T J (HeatCanonicalNative.locality T) W
    (HeatCanonicalNative.coordinate T) hWa t ht N (fun n hn => (ht hn).trans hTN.le)
  have hMsym : ∀ x y : Base, inner ℝ (noise b hb hbound x) y=inner ℝ x (noise b hb hbound y) :=
    (HeatMultiplierAdjoint.scalar_multiplier_self_adjoint baseMeasure b hb hbound).isSymmetric
  have hMnorm : ‖noise b hb hbound‖≤1 :=
    SHEStochastic.BoundedFieldOperator.operator_norm (HeatScalarMultiplier.field baseMeasure b hb hbound)
  obtain ⟨sol⟩ := HeatVariationalForwardModel.exists_solution F μ T (noise b hb hbound) basis J hT
    (HeatCanonicalNative.locality T) (HeatCanonicalNative.continuous_stopped T)
    HeatCanonicalNullComplete.contains_nulls (SHEStochastic.NativeScalarBDG.constant 3)
    (HeatCanonicalBDG.hilbert_bdg basis T 3) (fun s ω => paperB (Ue s ω)) hBU hBE g₀
  obtain ⟨back,hdual⟩ := HeatVariationalSystem.exists_adjoint F μ T (noise b hb hbound) basis J
    hMnorm hMsym
    HeatCanonicalNullComplete.contains_nulls (HeatCanonicalNative.locality T) W (HeatCanonicalNative.coordinate T)
    hWa (fun ω => ω.continuous) t ht ht0 N hN hstep hTN g₀ g hP (fun s ω => paperB (Ue s ω)) hBU hBE sol
  have hctrl : (∫ p,inner ℝ (paperB (Ue p.1 p.2)) (z p.1 p.2) ∂energyMeasure μ T)=
      (∫ p,inner ℝ (U p.1 p.2) (paperBstar (z p.1 p.2)) ∂energyMeasure μ T) := by
    apply integral_congr_ae
    filter_upwards [heq] with p hp
    change Ue p.1 p.2=U p.1 p.2 at hp
    rw [hp]
    exact HeatControlAdjointPairing.pairing _ _
  have hterm := HeatBackwardEndpointPairing.terminal μ T family family_continuous family_contraction (noise b hb hbound)
    paperHeat_zero W t N hN hstep hTN g (sol.weak.value T) (back.value T) (back.value_path T le_rfl)
  have hinit := HeatBackwardEndpointPairing.initial μ T family family_continuous family_contraction (noise b hb hbound)
    W t ht ht0 N hN hstep hTN g₀ g sol.weak.value back.value sol.weak.initial_value (back.value_path 0 zero_le)
  rw [hctrl,hinit] at hdual
  have hterminal := hterm.symm.trans hdual
  refine ⟨I,hBU,hBE,sol,back,?_⟩
  calc
    _ = ∫ ω,HeatBrownianProducts.products W t N ω*inner ℝ g (sol.weak.value T ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [sol.weak.path_version T le_rfl] with ω hω
      rw [hω]
    _ = _ := hterminal

end HeatCanonicalVariationalSystem
#check @HeatCanonicalVariationalSystem.exists_solution_and_duality
#print HeatCanonicalVariationalSystem.exists_solution_and_duality
#print axioms HeatCanonicalVariationalSystem.exists_solution_and_duality
