import HeatControlConvolution

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatControlJoint
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

include hS hcontr in
theorem measurable (f : ℝ≥0 × Ω → E) (hf : Measurable f) :
    StronglyMeasurable (fun p : ℝ≥0 × Ω => HeatControlConvolution.value H S f p.1 p.2) := by
  have hr := HeatVolterraKernel.raw_measurable S (ContinuousLinearMap.id ℝ E) hS hcontr f hf
  have hm : Measurable (fun p : ℝ≥0 × (ℝ≥0 × Ω) => (p.2.1,(p.1,p.2.2))) :=
    measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  exact (hr.comp hm).stronglyMeasurable.integral_prod_left'

include hS hcontr in
theorem integrable_of_version (f : ℝ≥0 × Ω → E) (hf : Measurable f)
    (X : ℝ≥0 → Ω → E) (hXm : StronglyMeasurable (Function.uncurry X))
    (D : Ω → ℝ) (hDm : MemLp D 2 μ) (hDb : ∀ t ω, ‖X t ω‖≤D ω)
    (hrep : ∀ t, X t=ᵐ[μ] HeatControlConvolution.value H S f t) (T : ℝ≥0) :
    Integrable (fun p : ℝ≥0 × Ω => HeatControlConvolution.value H S f p.1 p.2) (energyMeasure μ T) := by
  have hi : Integrable (Function.uncurry X) (energyMeasure μ T) :=
    ((hDm.integrable (by norm_num : (1:ENNReal)≤2)).comp_snd (timeMeasure T)).mono' hXm.aestronglyMeasurable
      (Eventually.of_forall (fun p => hDb p.1 p.2))
  have hm := measurable H S hS hcontr f hf
  have he : Function.uncurry X=ᵐ[energyMeasure μ T] fun p => HeatControlConvolution.value H S f p.1 p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hXm.measurable hm.measurable)).mpr
    exact Eventually.of_forall hrep
  exact hi.congr he

end HeatControlJoint
#check @HeatControlJoint.measurable
#print axioms HeatControlJoint.measurable
#check @HeatControlJoint.integrable_of_version
#print HeatControlJoint.integrable_of_version
#print axioms HeatControlJoint.integrable_of_version
