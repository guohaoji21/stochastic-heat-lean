import HeatVariationalForwardModel

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatVariationalProperties
open MeasureTheory Filter SHE.PredictableL2 HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolventForm
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatVariationalForwardModel.Solution F μ H M I U hU hE g)

theorem sobolev_representation :
    StronglyMeasurable[F.predictable] (sol.sobolev : ℝ≥0 × Ω → H01) ∧
    Integrable (fun p : ℝ≥0 × Ω => ‖sol.sobolev p‖^2) (energyMeasure μ H) ∧
    (fun p => embed (sol.sobolev p))=ᵐ[energyMeasure μ H] Function.uncurry sol.weak.path := by
  refine ⟨Lp.stronglyMeasurable sol.sobolev,
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp sol.sobolev)).norm.integrable_sq,?_⟩
  have he : (fun p => embed (sol.sobolev p))=ᵐ[energyMeasure μ H]
      HeatResolventH01Compact.embedProcess F μ H sol.sobolev := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (ae_eq_of_ae_eq_trim (embed.coeFn_compLpL sol.sobolev)).symm
  rw [sol.input_embedding] at he
  exact he.trans sol.weak.input_path

variable [IsSeparable μ]

theorem equation {T : ℝ≥0} (hT : T≤H) :
    (embed.adjoint.compLpL 2 μ) (sol.weak.value T)=Lp.const 2 μ (embed.adjoint g)+
      (embed.adjoint.compLpL 2 μ) (HeatAmbientDrift.value μ H (HeatControlAdapted.clamp U H)
        (HeatControlAdapted.clamp_measurable F U hU H).measurable
        (HeatClampedControl.square_integrable F μ H U hU hE) T)+
      (HeatH01WeakOperator.operator.compLpL 2 μ) (HeatH01VariationalEquation.integrated F μ H sol.sobolev T)+
      (embed.adjoint.compLpL 2 μ) (I.integral (SHE.StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.weak.input))) :=
  HeatH01VariationalEquation.equation F μ H M I U hU hE g sol.weak sol.sobolev sol.input_embedding hT

end HeatVariationalProperties
#check @HeatVariationalProperties.sobolev_representation
#print axioms HeatVariationalProperties.sobolev_representation
#check @HeatVariationalProperties.equation
#print HeatVariationalProperties.equation
#print axioms HeatVariationalProperties.equation
