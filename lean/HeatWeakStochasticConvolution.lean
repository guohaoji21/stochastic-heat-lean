import HeatWeakStochasticInput
import SHE.TerminalItoFubini

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatWeakStochasticConvolution
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

theorem weak_equation (u : Process (E := Base) F μ H) (φ ψ : Base)
    (hφ : weakLaplacian φ ψ) (T : ℝ≥0) :
    ((innerSL ℝ φ).compLpL 2 μ) ((I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M T u))=
      ((innerSL ℝ φ).compLpL 2 μ) ((I).integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M u)))+
      ∫ t,((innerSL ℝ ψ).compLpL 2 μ) ((I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u)) ∂timeMeasure T := by
  let A := HeatHilbertRandomStop.project F μ H (innerSL ℝ φ)
    (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M T u)
  let B := HeatHilbertRandomStop.project F μ H (innerSL ℝ φ)
    (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M u))
  let K := fun t => HeatHilbertRandomStop.project F μ H (innerSL ℝ ψ)
    (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u)
  have hinput := HeatWeakStochasticInput.input_identity F μ H M u φ ψ hφ T
  change (∫ t,K t ∂timeMeasure T)=A-B at hinput
  have he : A=B+∫ t,K t ∂timeMeasure T := by rw [hinput];abel
  have hnat (L : Base →L[ℝ] ℝ) (v : Process (E := Base) F μ H) :
      (L.compLpL 2 μ) ((I).integral v)=J.integral (HeatHilbertRandomStop.project F μ H L v) :=
    HeatTerminalNaturality.scalar_commutes F μ H basis J L v
  rw [hnat,hnat]
  change J.integral A=J.integral B+_
  rw [he,map_add,SHE.TerminalItoFubini.integral_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => (hnat (innerSL ℝ ψ)
    (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u)).symm)

end HeatWeakStochasticConvolution
#check @HeatWeakStochasticConvolution.weak_equation
#print HeatWeakStochasticConvolution.weak_equation
#print axioms HeatWeakStochasticConvolution.weak_equation
