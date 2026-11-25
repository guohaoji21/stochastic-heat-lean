import HeatL2PairingLimit
import HeatDualityPathMemLp
import HeatSampledApproximation
import HeatStrongL2

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatDualityLimits
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)
local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure;infer_instance

include hS hcontr in
theorem control (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (f : ℝ≥0 × Ω → E) (hfm : MemLp f 2 (energyMeasure μ H))
    (X : ℝ≥0 → Ω → E) (hc : ∀ ω, Continuous (fun t => X t ω)) (hm : ∀ t, Measurable (X t))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0≤D ω) (hB : ∀ t, t≤H → ∀ ω, ‖X t ω‖≤D ω) :
    Tendsto (fun n => ∫ p,inner ℝ (f p) (HeatDualityPathApprox.raw H S X n p) ∂energyMeasure μ H)
      atTop (𝓝 (∫ p,inner ℝ (f p) (X p.1 p.2) ∂energyMeasure μ H)) := by
  exact HeatL2PairingLimit.tends (energyMeasure μ H) f hfm _ (Function.uncurry X)
    (HeatDualityPathMemLp.approximation μ H X hc hm D hD hB S hS hcontr)
    (HeatDualityPathMemLp.state μ H X hc hm D hD hB)
    (HeatDualityPathApprox.approximation μ H S hS hcontr hzero X hc hm D hD hD0 hB)

include hS hcontr in
theorem drift (hzero : S 0=ContinuousLinearMap.id ℝ E) (M : E →L[ℝ] E)
    (V : ℝ≥0 → Lp E 2 μ) (hV : Continuous V) (u v : Process (E := E) F μ H)
    (hVu : ∀ᵐ s ∂timeMeasure H, (fun ω => u (s,ω))=ᵐ[μ] V s)
    (C : ℝ) (hC : ∀ s, s≤H → ‖V s‖≤C) :
    Tendsto (fun n => ∫ p,inner ℝ (M (v p)) (HeatSampledLp.raw μ H S V n p) ∂energyMeasure μ H)
      atTop (𝓝 (∫ p,inner ℝ (M (v p)) (u p) ∂energyMeasure μ H)) := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hv := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  exact HeatL2PairingLimit.tends (energyMeasure μ H) (fun p => M (v p)) (M.comp_memLp' hv) _ u
    (HeatSampledLp.square_integrable μ H S hS hcontr V C hC) hu
    (HeatSampledApproximation.approximation F μ H S hS hcontr hzero V hV u hVu C hC)

include hS hcontr in
theorem noise (hzero : S 0=ContinuousLinearMap.id ℝ E) (M : E →L[ℝ] E)
    (u v : Process (E := E) F μ H) :
    Tendsto (fun n => ∫ p,inner ℝ (M (u p)) (S (HeatDualityGrid.width n) (v p)) ∂energyMeasure μ H)
      atTop (𝓝 (∫ p,inner ℝ (M (u p)) (v p) ∂energyMeasure μ H)) := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hv := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  exact HeatL2PairingLimit.tends (energyMeasure μ H) (fun p => M (u p)) (M.comp_memLp' hu) _ v
    (fun n => (S (HeatDualityGrid.width n)).comp_memLp' hv) hv
    (HeatStrongL2.regularization (energyMeasure μ H) S hS hcontr hzero v hv _ HeatDualityGrid.width_tendsto)

end HeatDualityLimits
#check @HeatDualityLimits.control
#print axioms HeatDualityLimits.control
#check @HeatDualityLimits.drift
#print axioms HeatDualityLimits.drift
#check @HeatDualityLimits.noise
#print HeatDualityLimits.noise
#print axioms HeatDualityLimits.noise
