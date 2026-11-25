import HeatSampledLp

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatSampledApproximation
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

include hS hcontr in
theorem approximation (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (V : ℝ≥0 → Lp E 2 μ) (hV : Continuous V) (u : Process (E := E) F μ H)
    (hVu : ∀ᵐ s ∂timeMeasure H, (fun ω => u (s,ω))=ᵐ[μ] V s)
    (C : ℝ) (hC : ∀ s, s≤H → ‖V s‖≤C) :
    Tendsto (fun n => ∫ p, ‖HeatSampledLp.raw μ H S V n p-u p‖^2 ∂energyMeasure μ H) atTop (𝓝 0) := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have he (n : ℕ) : (∫ p, ‖HeatSampledLp.raw μ H S V n p-u p‖^2 ∂energyMeasure μ H)=
      ∫ s,HeatDualityMeanSquare.error μ H S V n s ∂timeMeasure H := by
    have hraw := HeatSampledLp.square_integrable μ H S hS hcontr V C hC n
    have hi : Integrable (fun p => ‖HeatSampledLp.raw μ H S V n p-u p‖^2) (energyMeasure μ H) :=
      (hraw.sub hu).norm.integrable_sq
    change (∫ p, ‖HeatSampledLp.raw μ H S V n p-u p‖^2 ∂(timeMeasure H).prod μ)=_
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [hVu] with s hs
    let R := HeatLiftedSemigroup.family μ S (HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s))
      (V (HeatDualityEndpoints.left H n s))
    change (∫ ω,‖HeatSampledLp.raw μ H S V n (s,ω)-u (s,ω)‖^2 ∂μ)=‖R-V s‖^2
    rw [realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [HeatSampledLp.raw_ae μ H S V n s,hs,Lp.coeFn_sub R (V s)] with ω hr hu hsub
    rw [hsub]
    change ‖HeatSampledLp.raw μ H S V n (s,ω)-u (s,ω)‖^2=‖R ω-V s ω‖^2
    rw [hr,hu]
  have h := HeatDualityMeanSquare.approximation μ H S hS hcontr hzero V hV C hC
  exact h.congr' (Eventually.of_forall (fun n => (he n).symm))

end HeatSampledApproximation
#check @HeatSampledApproximation.approximation
#print HeatSampledApproximation.approximation
#print axioms HeatSampledApproximation.approximation
