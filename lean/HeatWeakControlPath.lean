import HeatWeakDeterministicConvolution
import HeatTimeRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatWeakControlPath
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatIntervalNormalization
open HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

theorem weak_equation {H T : ℝ≥0} (hT : T≤H) (f : ℝ≥0 → Base) (hfm : Measurable f)
    (hfi : Integrable f (timeMeasure H)) (φ ψ : Base) (hφ : weakLaplacian φ ψ) :
    Integrable (fun t => inner ℝ ψ (HeatWeakDeterministicConvolution.value H f t)) (timeMeasure T) ∧
      inner ℝ φ (HeatWeakDeterministicConvolution.value H f T)=
        inner ℝ φ (∫ s,f s ∂timeMeasure T)+
          ∫ t,inner ℝ ψ (HeatWeakDeterministicConvolution.value H f t) ∂timeMeasure T := by
  have hi : Integrable f (timeMeasure T) := hfi.mono_measure (HeatTimeRestriction.mono hT)
  have hr (t : ℝ≥0) (ht : t≤T) : HeatWeakDeterministicConvolution.value H f t=
      HeatWeakDeterministicConvolution.value T f t :=
    HeatTimeRestriction.control_value family (fun p : ℝ≥0 × Unit => f p.1) ht hT ()
  have he : (fun t => inner ℝ ψ (HeatWeakDeterministicConvolution.value H f t))=ᵐ[timeMeasure T]
      fun t => inner ℝ ψ (HeatWeakDeterministicConvolution.value T f t) := by
    filter_upwards [timeMeasure_ae_mem T] with t ht
    exact congrArg (inner ℝ ψ) (hr t ht.2)
  obtain ⟨hInt,hEq⟩ := HeatWeakDeterministicConvolution.weak_equation T f hfm hi φ ψ hφ
  refine ⟨hInt.congr he.symm,?_⟩
  rw [hr T le_rfl,integral_congr_ae he]
  rw [←integral_inner (𝕜 := ℝ) hi φ]
  exact hEq

end HeatWeakControlPath
#check @HeatWeakControlPath.weak_equation
#print HeatWeakControlPath.weak_equation
#print axioms HeatWeakControlPath.weak_equation
