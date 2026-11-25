import HeatWeakKernel
import HeatVolterraKernel
import HeatVolterraModel

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatWeakRawIntegral
open MeasureTheory Filter Set HeatIntervalNormalization HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal

theorem integral_raw {Ω : Type*} (u : ℝ≥0 × Ω → Base) (M : Base →L[ℝ] Base)
    (φ ψ : Base) (hφ : weakLaplacian φ ψ) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    (∫ t,inner ℝ ψ (HeatVolterraKernel.raw family M u (t,p)) ∂SHE.PredictableL2.timeMeasure T)=
      inner ℝ φ (HeatVolterraKernel.raw family M u (T,p))-
        (if p.1<T then inner ℝ φ (M (u p)) else 0) := by
  by_cases hp : p.1<T
  · have he : (fun t => inner ℝ ψ (HeatVolterraKernel.raw family M u (t,p)))=ᵐ[SHE.PredictableL2.timeMeasure T]
        (Ioc p.1 T).indicator (fun t => inner ℝ ψ (family (t-p.1) (M (u p)))) := by
      filter_upwards [SHE.PredictableL2.timeMeasure_ae_mem T] with t ht
      by_cases hpt : p.1<t
      · rw [indicator_of_mem (show t∈Ioc p.1 T from ⟨hpt,ht.2⟩)]
        simp only [HeatVolterraKernel.raw,if_pos hpt]
      · rw [indicator_of_notMem (show t∉Ioc p.1 T from fun h => hpt h.1)]
        simp only [HeatVolterraKernel.raw,if_neg hpt,inner_zero_right]
    rw [integral_congr_ae he,integral_indicator measurableSet_Ioc]
    simp only [HeatVolterraKernel.raw,if_pos hp]
    exact (HeatWeakKernel.integrated_test (M (u p)) φ ψ hφ hp.le le_rfl).symm
  · have he : (fun t => inner ℝ ψ (HeatVolterraKernel.raw family M u (t,p)))=ᵐ[SHE.PredictableL2.timeMeasure T] 0 := by
      filter_upwards [SHE.PredictableL2.timeMeasure_ae_mem T] with t ht
      have hn : ¬p.1<t := fun h => hp (h.trans_le ht.2)
      simp only [HeatVolterraKernel.raw,if_neg hn,inner_zero_right,Pi.zero_apply]
    rw [integral_congr_ae he]
    simp only [HeatVolterraKernel.raw,if_neg hp,inner_zero_right,Pi.zero_apply,integral_zero,sub_zero]

end HeatWeakRawIntegral
#check @HeatWeakRawIntegral.integral_raw
#print HeatWeakRawIntegral.integral_raw
#print axioms HeatWeakRawIntegral.integral_raw
