import HeatDualityGrid
import HeatPredictableSemigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatStrongL2
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
variable {P E : Type*} [MeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (ν : Measure P) [IsFiniteMeasure ν]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

include hS hcontr in
theorem regularization (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (f : P → E) (hf : MemLp f 2 ν) (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,‖S (ε n) (f p)-f p‖^2 ∂ν) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun p => ‖S (ε n) (f p)-f p‖^2) ν :=
    (((S (ε n)).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub hf.aestronglyMeasurable).norm.pow 2
  have hb (n : ℕ) : ∀ᵐ p ∂ν, ‖‖S (ε n) (f p)-f p‖^2‖≤4*‖f p‖^2 := by
    exact Eventually.of_forall (fun p => by
      have hh : ‖S (ε n) (f p)-f p‖≤2*‖f p‖ := (norm_sub_le _ _).trans (by linarith [hcontr (ε n) (f p)])
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by ring))
  have hl : ∀ᵐ p ∂ν, Tendsto (fun n => ‖S (ε n) (f p)-f p‖^2) atTop (𝓝 0) := by
    exact Eventually.of_forall (fun p => by
      have hh := (((hS (f p)).continuousAt.tendsto.comp hε).sub_const (f p)).norm.pow 2
      simpa only [Function.comp_apply,hzero,ContinuousLinearMap.id_apply,sub_self,norm_zero,zero_pow (by omega : 2≠0)] using hh)
  have he := tendsto_integral_of_dominated_convergence (fun p => 4*‖f p‖^2)
    hm (hf.norm.integrable_sq.const_mul 4) hb hl
  simpa only [integral_zero] using he

end HeatStrongL2
#check @HeatStrongL2.regularization
#print HeatStrongL2.regularization
#print axioms HeatStrongL2.regularization
