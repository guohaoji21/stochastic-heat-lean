import HeatWeakForwardModel
import HeatDirichletResolvent
import HeatLpSpatialExt
import HeatScalarLpConst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatRegularizedWeakEquation
open MeasureTheory Filter SHE SHE.PredictableL2 HeatIntervalNormalization HeatWeakDirichlet
open HeatDirichletResolvent
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

def derivative (a : ℝ) (ha : 1≤a) : Base →L[ℝ] Base := a • (smoothing a ha-ContinuousLinearMap.id ℝ Base)

theorem derivative_symmetric {a : ℝ} (ha : 1≤a) (x y : Base) :
    inner ℝ (derivative a ha x) y=inner ℝ x (derivative a ha y) := by
  change inner ℝ (a • (smoothing a ha x-x)) y=inner ℝ x (a • (smoothing a ha y-y))
  simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right]
  rw [smoothing_symmetric ha]

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (I : StandardTerminalIto (C := Base) (E := Base) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M I U hU hE g)

theorem equation {a : ℝ} (ha : 1≤a) {T : ℝ≥0} (hT : T≤H) :
    ((smoothing a ha).compLpL 2 μ) (sol.value T)=Lp.const 2 μ (smoothing a ha g)+
      ((smoothing a ha).compLpL 2 μ) (HeatAmbientDrift.value μ H (HeatControlAdapted.clamp U H)
        (HeatControlAdapted.clamp_measurable F U hU H).measurable (HeatClampedControl.square_integrable F μ H U hU hE) T)+
      (∫ t,((derivative a ha).compLpL 2 μ) (sol.value t) ∂timeMeasure T)+
      ((smoothing a ha).compLpL 2 μ) (I.integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.input))) := by
  apply HeatLpSpatialExt.ext μ
  intro φ
  have hw := sol.weak_equation T hT (smoothing a ha φ) (derivative a ha φ) (smoothing_graph ha φ)
  rw [HeatLpSpatialExt.scalar_compLp μ (smoothing a ha) (smoothing_symmetric ha) φ,
    HeatLpSpatialExt.scalar_compLp μ (smoothing a ha) (smoothing_symmetric ha) φ,
    HeatLpSpatialExt.scalar_compLp μ (smoothing a ha) (smoothing_symmetric ha) φ] at hw
  simp_rw [HeatLpSpatialExt.scalar_compLp μ (derivative a ha) (derivative_symmetric ha) φ] at hw
  rw [smoothing_symmetric ha φ g] at hw
  rw [map_add,map_add,map_add,HeatScalarLpConst.map_const]
  have hi : Integrable (fun t => ((derivative a ha).compLpL 2 μ) (sol.value t)) (timeMeasure T) :=
    HeatCompactTimeIntegrability.of_continuous _ (((derivative a ha).compLpL 2 μ).continuous.comp sol.mean_square_continuous) T
  rw [←((innerSL ℝ φ).compLpL 2 μ).integral_comp_comm hi]
  exact hw

end HeatRegularizedWeakEquation
#check @HeatRegularizedWeakEquation.derivative_symmetric
#print axioms HeatRegularizedWeakEquation.derivative_symmetric
#check @HeatRegularizedWeakEquation.equation
#print HeatRegularizedWeakEquation.equation
#print axioms HeatRegularizedWeakEquation.equation
