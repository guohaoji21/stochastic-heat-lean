import HeatWeakPairing
import HeatTimeTranslation

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatWeakKernel
open MeasureTheory HeatIntervalNormalization HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal

theorem integrated_test (x φ ψ : Base) (hφ : weakLaplacian φ ψ)
    {H s T : ℝ≥0} (hsT : s≤T) (hTH : T≤H) :
    inner ℝ φ (family (T-s) x)-inner ℝ φ x=
      ∫ r in Set.Ioc s T,inner ℝ ψ (family (r-s) x) ∂SHE.PredictableL2.timeMeasure H := by
  rw [HeatTimeTranslation.integral_shift (fun r => inner ℝ ψ (family r x)) hsT hTH]
  simpa only [real_inner_comm] using HeatWeakPairing.integrated_test x φ ψ hφ (T-s)

end HeatWeakKernel
#check @HeatWeakKernel.integrated_test
#print HeatWeakKernel.integrated_test
#print axioms HeatWeakKernel.integrated_test
