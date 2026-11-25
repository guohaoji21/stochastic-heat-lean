import HeatH01WeakOperator
import HeatH01TimeField
import HeatLpDenseExt

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatH01VariationalEquation
open MeasureTheory Filter SHE SHE.PredictableL2 HeatIntervalNormalization
open HeatWeakDirichlet HeatDirichletResolventForm
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : MeasurableSpace H01 := borel H01
local instance : BorelSpace H01 := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : SecondCountableTopology H01 := by unfold H01;infer_instance
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (I : StandardTerminalIto (C := Base) (E := Base) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M I U hU hE g)
  (v : Process (E := H01) F μ H)

def integrated (T : ℝ≥0) : Lp H01 2 μ := ∫ t,HeatH01TimeField.value F μ H v t ∂timeMeasure T

theorem laplace_integral (hv : HeatResolventH01Compact.embedProcess F μ H v=sol.input)
    {T : ℝ≥0} (hT : T≤H) (φ : H01) (ψ : Base) (hg : weakLaplacian (embed φ) ψ) :
    ((innerSL ℝ φ).compLpL 2 μ) ((HeatH01WeakOperator.operator.compLpL 2 μ) (integrated F μ H v T))=
      ∫ t,((innerSL ℝ ψ).compLpL 2 μ) (sol.value t) ∂timeMeasure T := by
  rw [HeatTerminalNaturality.compLp_comp,HeatH01WeakOperator.graph_pairing φ ψ hg]
  rw [←HeatTerminalNaturality.compLp_comp]
  have hi := HeatH01TimeField.integrable F μ H v hT
  have he := HeatH01TimeField.embed_slices F μ H v sol.input sol.value hv sol.input_slices
  have heT : ∀ᵐ t ∂timeMeasure T, (embed.compLpL 2 μ) (HeatH01TimeField.value F μ H v t)=sol.value t :=
    he.filter_mono (ae_mono (HeatTimeRestriction.mono hT))
  let L := ((innerSL ℝ ψ).compLpL 2 μ).comp (embed.compLpL 2 μ)
  have hc := L.integral_comp_comm hi
  change (∫ t,((innerSL ℝ ψ).compLpL 2 μ) ((embed.compLpL 2 μ) (HeatH01TimeField.value F μ H v t)) ∂timeMeasure T)=
    ((innerSL ℝ ψ).compLpL 2 μ) ((embed.compLpL 2 μ) (integrated F μ H v T)) at hc
  rw [←hc]
  apply integral_congr_ae
  filter_upwards [heT] with t ht
  rw [ht]

theorem equation (hv : HeatResolventH01Compact.embedProcess F μ H v=sol.input)
    {T : ℝ≥0} (hT : T≤H) :
    (embed.adjoint.compLpL 2 μ) (sol.value T)=Lp.const 2 μ (embed.adjoint g)+
      (embed.adjoint.compLpL 2 μ) (HeatAmbientDrift.value μ H (HeatControlAdapted.clamp U H)
        (HeatControlAdapted.clamp_measurable F U hU H).measurable
        (HeatClampedControl.square_integrable F μ H U hU hE) T)+
      (HeatH01WeakOperator.operator.compLpL 2 μ) (integrated F μ H v T)+
      (embed.adjoint.compLpL 2 μ) (I.integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.input))) := by
  apply HeatLpDenseExt.ext μ (lift 1 (le_refl 1)) HeatDirichletH01Core.lift_one_dense
  intro f
  let φ := lift 1 (le_refl 1) f
  let ψ := embed φ-f
  have hg : weakLaplacian (embed φ) ψ := HeatDirichletH01Core.weak_graph_lift_one f
  have hweak := sol.weak_equation T hT (embed φ) ψ hg
  have hgrad := laplace_integral F μ H M I U hU hE g sol v hv hT φ ψ hg
  simp only [map_add,HeatTerminalNaturality.compLp_comp,HeatH01WeakOperator.adjoint_pairing,
    HeatScalarLpConst.map_const]
  change ((innerSL ℝ (embed φ)).compLpL 2 μ) (sol.value T)=_
  rw [HeatTerminalNaturality.compLp_comp] at hgrad
  rw [hgrad]
  have hconst : (innerSL ℝ φ) (embed.adjoint g)=inner ℝ (embed φ) g := embed.adjoint_inner_right φ g
  rw [hconst]
  exact hweak

end HeatH01VariationalEquation
#check @HeatH01VariationalEquation.laplace_integral
#print axioms HeatH01VariationalEquation.laplace_integral
#check @HeatH01VariationalEquation.equation
#print HeatH01VariationalEquation.equation
#print axioms HeatH01VariationalEquation.equation
