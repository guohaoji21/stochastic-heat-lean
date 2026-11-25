import HeatDualityPathApprox

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatDualityPathMemLp
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (X : ℝ≥0 → Ω → E) (hc : ∀ ω, Continuous (fun t => X t ω)) (hm : ∀ t, Measurable (X t))
  (D : Ω → ℝ) (hD : MemLp D 2 μ) (hB : ∀ t, t≤H → ∀ ω, ‖X t ω‖≤D ω)

include hc hm hD hB in
theorem state : MemLp (Function.uncurry X) 2 (energyMeasure μ H) := by
  have hX := measurable_uncurry_of_continuous_of_measurable hc hm
  apply (hD.comp_snd (timeMeasure H)).mono' hX.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
  exact hB _ hp.2 _

variable (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)
include hc hm hD hB hS hcontr in
theorem approximation (n : ℕ) : MemLp (HeatDualityPathApprox.raw H S X n) 2 (energyMeasure μ H) := by
  have hX := measurable_uncurry_of_continuous_of_measurable hc hm
  have hr : Measurable (fun p : ℝ≥0 × Ω => HeatDualityEndpoints.right H n p.1) :=
    (HeatDualityEndpoints.measurable H n).2.comp measurable_fst
  have ht : Measurable (fun p : ℝ≥0 × Ω => HeatDualityGrid.width n+(HeatDualityEndpoints.right H n p.1-p.1)) :=
    measurable_const.add (hr.sub measurable_fst)
  have hraw : Measurable (HeatDualityPathApprox.raw H S X n) :=
    (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
      (ht.prodMk (hX.comp (hr.prodMk measurable_snd)))
  apply (hD.comp_snd (timeMeasure H)).mono' hraw.stronglyMeasurable.aestronglyMeasurable
  exact Eventually.of_forall (fun p => (hcontr _ _).trans (hB _ (min_le_right _ _) _))

end HeatDualityPathMemLp
#check @HeatDualityPathMemLp.state
#print axioms HeatDualityPathMemLp.state
#check @HeatDualityPathMemLp.approximation
#print HeatDualityPathMemLp.approximation
#print axioms HeatDualityPathMemLp.approximation
