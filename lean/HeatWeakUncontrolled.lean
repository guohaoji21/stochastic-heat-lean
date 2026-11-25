import HeatWeakStochasticConvolution
import HeatScalarLpConst

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatWeakUncontrolled
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem weak_equation (g : Base) (u : Process (E := Base) F μ H) (φ ψ : Base)
    (hφ : weakLaplacian φ ψ) (T : ℝ≥0) :
    let V := HeatMildSolution.value F μ H family family_continuous family_contraction M (I) g u
    ((innerSL ℝ φ).compLpL 2 μ) (V T)=Lp.const 2 μ (inner ℝ φ g)+
      (∫ t,((innerSL ℝ ψ).compLpL 2 μ) (V t) ∂timeMeasure T)+
      ((innerSL ℝ φ).compLpL 2 μ) ((I).integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M u))) := by
  let V := HeatMildSolution.value F μ H family family_continuous family_contraction M (I) g u
  let N := fun t => (I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u)
  let P := (innerSL ℝ ψ).compLpL 2 μ
  let C : ℝ →L[ℝ] Lp ℝ 2 μ := Lp.constL 2 μ ℝ
  have hVi (t : ℝ≥0) : P (V t)=Lp.const 2 μ (inner ℝ ψ (family t g))+P (N t) := by
    change P (Lp.const 2 μ (family t g)+N t)=_
    rw [map_add,HeatScalarLpConst.map_const]
    rfl
  have hc : Integrable (fun t => Lp.const 2 μ (inner ℝ ψ (family t g))) (timeMeasure T) :=
    C.integrable_comp ((HeatWeakPairing.orbit_integrable g T).const_inner ψ)
  have hn : Integrable (fun t => P (N t)) (timeMeasure T) :=
    (P.comp (I).integral.toContinuousLinearMap).integrable_comp
      (HeatSliceNorm.integrable F μ H family family_continuous family_contraction M u T)
  have hsum : (∫ t,P (V t) ∂timeMeasure T)=
      Lp.const 2 μ (∫ t,inner ℝ ψ (family t g) ∂timeMeasure T)+(∫ t,P (N t) ∂timeMeasure T) := by
    rw [integral_congr_ae (Eventually.of_forall hVi),integral_add hc hn]
    congr 1
    exact C.integral_comp_comm ((HeatWeakPairing.orbit_integrable g T).const_inner ψ)
  have horbit : inner ℝ φ (family T g)=inner ℝ φ g+∫ t,inner ℝ ψ (family t g) ∂timeMeasure T := by
    have he : inner ℝ φ (family T g)-inner ℝ φ g=∫ t,inner ℝ ψ (family t g) ∂timeMeasure T := by
      simpa only [real_inner_comm] using HeatWeakPairing.integrated_test g φ ψ hφ T
    linarith
  have hconst : Lp.const 2 μ (inner ℝ φ (family T g))=
      Lp.const 2 μ (inner ℝ φ g)+Lp.const 2 μ (∫ t,inner ℝ ψ (family t g) ∂timeMeasure T) := by
    have he := congrArg C horbit
    rw [map_add] at he
    exact he
  have hnoise := HeatWeakStochasticConvolution.weak_equation F μ H M basis J u φ ψ hφ T
  change ((innerSL ℝ φ).compLpL 2 μ) (V T)=_
  change ((innerSL ℝ φ).compLpL 2 μ) (Lp.const 2 μ (family T g)+N T)=_
  rw [map_add,HeatScalarLpConst.map_const]
  change Lp.const 2 μ (inner ℝ φ (family T g))+((innerSL ℝ φ).compLpL 2 μ) (N T)=_
  rw [hconst]
  change Lp.const 2 μ (inner ℝ φ g)+Lp.const 2 μ (∫ t,inner ℝ ψ (family t g) ∂timeMeasure T)+
    ((innerSL ℝ φ).compLpL 2 μ) (N T)=Lp.const 2 μ (inner ℝ φ g)+(∫ t,P (V t) ∂timeMeasure T)+_
  rw [hsum,hnoise]
  abel

end HeatWeakUncontrolled
#check @HeatWeakUncontrolled.weak_equation
#print HeatWeakUncontrolled.weak_equation
#print axioms HeatWeakUncontrolled.weak_equation
