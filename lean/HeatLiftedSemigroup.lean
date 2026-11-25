import HeatVolterraSlice
import HeatPredictableSemigroup

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatLiftedSemigroup
open MeasureTheory Filter
open scoped NNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

def family (t : ℝ≥0) : Lp E 2 μ →L[ℝ] Lp E 2 μ := (S t).compLpL 2 μ

include hcontr in
theorem contraction (t : ℝ≥0) (X : Lp E 2 μ) : ‖family μ S t X‖≤‖X‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(S t).coeFn_compLpL X] with ω hω
  change ‖((S t).compLpL 2 μ) X ω‖≤‖X ω‖
  rw [hω]
  exact hcontr _ _

include hS hcontr in
theorem continuous (X : Lp E 2 μ) : Continuous (fun t => family μ S t X) := by
  apply continuous_iff_seqContinuous.mpr
  intro a t ha
  apply HeatVolterraSlice.dominated_Lp_convergence μ (fun n => family μ S (a n) X) (family μ S t X) X
  · intro n
    filter_upwards [(S (a n)).coeFn_compLpL X] with ω hω
    change ‖((S (a n)).compLpL 2 μ) X ω‖≤‖X ω‖
    rw [hω]
    exact hcontr _ _
  · filter_upwards [ae_all_iff.mpr (fun n => (S (a n)).coeFn_compLpL X),
      (S t).coeFn_compLpL X] with ω hn ht
    have he : (fun n => family μ S (a n) X ω)=(fun n => S (a n) (X ω)) := funext hn
    change Tendsto (fun n => family μ S (a n) X ω) atTop (𝓝 (family μ S t X ω))
    rw [he]
    change Tendsto (fun n => S (a n) (X ω)) atTop (𝓝 (((S t).compLpL 2 μ) X ω))
    rw [ht]
    exact (hS (X ω)).continuousAt.tendsto.comp ha

include hS hcontr in
theorem continuous_action : Continuous (fun p : ℝ≥0 × Lp E 2 μ => family μ S p.1 p.2) :=
  HeatPredictableSemigroup.continuous_action (family μ S) (continuous μ S hS hcontr) (contraction μ S hcontr)

end HeatLiftedSemigroup
#check @HeatLiftedSemigroup.contraction
#print axioms HeatLiftedSemigroup.contraction
#check @HeatLiftedSemigroup.continuous
#print axioms HeatLiftedSemigroup.continuous
#check @HeatLiftedSemigroup.continuous_action
#print axioms HeatLiftedSemigroup.continuous_action
