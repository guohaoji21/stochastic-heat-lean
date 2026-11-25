import HeatConstructedWeakContinuous

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace HeatWeakForwardModel
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (I : StandardTerminalIto (C := Base) (E := Base) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)

structure Solution where
  forcing : Process (E := Base) F μ H
  input : Process (E := Base) F μ H
  value : ℝ≥0 → Lp Base 2 μ
  path : ℝ≥0 → Ω → Base
  fixed_point : input=HeatVolterraForcing.orbit F μ H family family_continuous family_contraction g+forcing+
    HeatVolterraFixedPoint.convolution F μ H family family_continuous family_contraction M family_semigroup I input
  mean_square_continuous : Continuous value
  initial_value : value 0=Lp.const 2 μ g
  adapted_values : ∀ t, ∃ Z : Ω → Base, StronglyMeasurable[F t] Z ∧ value t=ᵐ[μ] Z
  input_slices : ∀ᵐ t ∂timeMeasure H, (fun ω => input (t,ω))=ᵐ[μ] value t
  mild_equation : ∀ t, value t=ᵐ[μ] fun ω => family t g+
    HeatControlConvolution.value H family (HeatControlAdapted.clamp U H) t ω+
    I.integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t input) ω
  path_continuous : ∀ ω, Continuous (fun t => path t ω)
  path_adapted : StronglyAdapted F path
  path_predictable : StronglyMeasurable[F.predictable] (Function.uncurry path)
  path_initial : path 0=ᵐ[μ] fun _ => g
  input_path : input=ᵐ[energyMeasure μ H] Function.uncurry path
  path_energy : Integrable (fun p : ℝ≥0 × Ω => ‖path p.1 p.2‖^2) (energyMeasure μ H)
  path_version : ∀ t, t≤H → path t=ᵐ[μ] value t
  weak_equation : ∀ T : ℝ≥0, T≤H → ∀ φ ψ : Base, weakLaplacian φ ψ →
    ((innerSL ℝ φ).compLpL 2 μ) (value T)=Lp.const 2 μ (inner ℝ φ g)+
      ((innerSL ℝ φ).compLpL 2 μ) (HeatAmbientDrift.value μ H (HeatControlAdapted.clamp U H)
        (HeatControlAdapted.clamp_measurable F U hU H).measurable
        (HeatClampedControl.square_integrable F μ H U hU hE) T)+
      (∫ t,((innerSL ℝ ψ).compLpL 2 μ) (value t) ∂timeMeasure T)+
      ((innerSL ℝ φ).compLpL 2 μ) (I.integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M input)))

end HeatWeakForwardModel
namespace HeatWeakForwardModel
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]

theorem exists_solution (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (hH : 0<H) (hlocal : StandardTerminalPastLocality J) (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 (HeatTerminalNaturality.integral F μ H basis J) B)
    (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base) :
    Nonempty (Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g) := by
  obtain ⟨A,u,V,hu,hVc,hV0,hVa,hVs,hVr,Y,hYc,hYa,hYp,hY0,hueq,hEn,hYV,hweak⟩ :=
    HeatConstructedWeakContinuous.exists_solution F μ H M basis J hH hlocal hversions hnull B hB U hU hE g
  exact ⟨⟨A,u,V,Y,hu,hVc,hV0,hVa,hVs,hVr,hYc,hYa,hYp,hY0,hueq,hEn,hYV,hweak⟩⟩

end HeatWeakForwardModel
#check @HeatWeakForwardModel.exists_solution
#print HeatWeakForwardModel.exists_solution
#print axioms HeatWeakForwardModel.exists_solution
