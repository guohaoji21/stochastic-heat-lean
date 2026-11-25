import HeatDualityEndpoints
import HeatLiftedSemigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatDualityMeanSquare
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

def error (V : ℝ≥0 → Lp E 2 μ) (n : ℕ) (s : ℝ≥0) : ℝ :=
  ‖HeatLiftedSemigroup.family μ S (HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s))
    (V (HeatDualityEndpoints.left H n s))-V s‖^2

include hS hcontr in
theorem approximation (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (V : ℝ≥0 → Lp E 2 μ) (hV : Continuous V) (C : ℝ)
    (hC : ∀ s, s≤H → ‖V s‖≤C) :
    Tendsto (fun n => ∫ s,error μ H S V n s ∂timeMeasure H) atTop (𝓝 0) := by
  have hC0 : 0≤C := (norm_nonneg _).trans (hC 0 zero_le)
  have hmeas (n : ℕ) : StronglyMeasurable (error μ H S V n) := by
    have hi : Measurable (ApproximationCells.index n) :=
      Nat.measurable_ceil.comp (measurable_coe_nnreal_real.div_const (ApproximationClock.delta n))
    have hvleft : StronglyMeasurable (fun s => V (HeatDualityEndpoints.left H n s)) :=
      (StronglyMeasurable.of_discrete (f := fun k : ℕ => V (HeatDualityGrid.point H n (k-1)))).comp_measurable hi
    have ht : StronglyMeasurable (fun s : ℝ≥0 => HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s)) :=
      (measurable_const.add (measurable_id.sub (HeatDualityEndpoints.measurable H n).1)).stronglyMeasurable
    exact (((HeatLiftedSemigroup.continuous_action μ S hS hcontr).comp_stronglyMeasurable
      (ht.prodMk hvleft)).sub hV.stronglyMeasurable).norm.pow 2
  have hb (n : ℕ) : ∀ᵐ s ∂timeMeasure H, ‖error μ H S V n s‖≤(2*C)^2 := by
    filter_upwards [timeMeasure_ae_mem H] with s hs
    have hl : HeatDualityEndpoints.left H n s≤H := min_le_right _ _
    have hbound : ‖HeatLiftedSemigroup.family μ S
        (HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s))
        (V (HeatDualityEndpoints.left H n s))-V s‖≤2*C :=
      (norm_sub_le _ _).trans (by
        have hc := HeatLiftedSemigroup.contraction μ S hcontr
          (HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s)) (V (HeatDualityEndpoints.left H n s))
        linarith [hC _ hl,hC s hs.2])
    change ‖‖_‖^2‖≤_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hlim : ∀ᵐ s ∂timeMeasure H, Tendsto (fun n => error μ H S V n s) atTop (𝓝 0) := by
    filter_upwards [timeMeasure_ae_mem H] with s hs
    have hl := HeatDualityEndpoints.left_tendsto H hs.1 hs.2
    have hconst : Tendsto (fun _ : ℕ => s) atTop (𝓝 s) := tendsto_const_nhds
    have htime : Tendsto (fun n => HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply,tsub_self,add_zero] using HeatDualityGrid.width_tendsto.add (hconst.sub hl)
    have hval := (HeatLiftedSemigroup.continuous_action μ S hS hcontr).tendsto (0,V s) |>.comp
      (htime.prodMk_nhds (hV.continuousAt.tendsto.comp hl))
    have hz : HeatLiftedSemigroup.family μ S 0 (V s)=V s := by
      apply Lp.ext
      filter_upwards [(S 0).coeFn_compLpL (V s)] with ω hω
      change ((S 0).compLpL 2 μ) (V s) ω=V s ω
      rw [hω,hzero]
      rfl
    have he := (hval.sub_const (V s)).norm.pow 2
    simpa only [error,Function.comp_apply,hz,sub_self,norm_zero,zero_pow (by omega : 2≠0)] using he
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ≥0 => (2*C)^2)
    (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _) hb hlim
  simpa only [integral_zero] using hi

end HeatDualityMeanSquare
#check @HeatDualityMeanSquare.approximation
#print HeatDualityMeanSquare.approximation
#print axioms HeatDualityMeanSquare.approximation
