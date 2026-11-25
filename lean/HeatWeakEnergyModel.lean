import HeatWeakForwardModel
import HeatConstructedWeakContinuous

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace HeatWeakEnergyModel
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
  input : Process (E := Base) F μ H
  value : ℝ≥0 → Lp Base 2 μ
  path : ℝ≥0 → Ω → Base
  mean_square_continuous : Continuous value
  initial_value : value 0=Lp.const 2 μ g
  adapted_values : ∀ t, ∃ Z : Ω → Base, StronglyMeasurable[F t] Z ∧ value t=ᵐ[μ] Z
  input_slices : ∀ᵐ t ∂timeMeasure H, (fun ω => input (t,ω))=ᵐ[μ] value t
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


def of_weak (sol : HeatWeakForwardModel.Solution F μ H M I U hU hE g) :
    Solution F μ H M I U hU hE g where
  input := sol.input
  value := sol.value
  path := sol.path
  mean_square_continuous := sol.mean_square_continuous
  initial_value := sol.initial_value
  adapted_values := sol.adapted_values
  input_slices := sol.input_slices
  path_continuous := sol.path_continuous
  path_adapted := sol.path_adapted
  path_predictable := sol.path_predictable
  path_initial := sol.path_initial
  input_path := sol.input_path
  path_energy := sol.path_energy
  path_version := sol.path_version
  weak_equation := sol.weak_equation

end HeatWeakEnergyModel
#print HeatWeakEnergyModel.Solution
