import SHE.PredictableTime
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
namespace HeatPartitionIntegral
open MeasureTheory Set SHE.PredictableL2
open scoped NNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem cells {H : ℝ≥0} (f : ℝ≥0 → E) (hf : Integrable f (timeMeasure H))
    (t : ℕ → ℝ≥0) (ht : Monotone t) : ∀ N,
    (∑ n∈Finset.range N,∫ s in Ioc (t n) (t (n+1)),f s ∂timeMeasure H)=
      ∫ s in Ioc (t 0) (t N),f s ∂timeMeasure H := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,←setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      hf.integrableOn hf.integrableOn,Ioc_union_Ioc_eq_Ioc (ht (Nat.zero_le N)) (ht (Nat.le_succ N))]

theorem whole {H : ℝ≥0} (f : ℝ≥0 → E) (hf : Integrable f (timeMeasure H))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hTN : t N=H) :
    (∑ n∈Finset.range N,∫ s in Ioc (t n) (t (n+1)),f s ∂timeMeasure H)=∫ s,f s ∂timeMeasure H := by
  rw [cells f hf t ht N,ht0,hTN,←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with s hs
  exact Set.indicator_of_mem hs f

end HeatPartitionIntegral
#check @HeatPartitionIntegral.cells
#print axioms HeatPartitionIntegral.cells
#check @HeatPartitionIntegral.whole
#print axioms HeatPartitionIntegral.whole
