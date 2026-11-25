import HeatDeterministicConvolution

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatControlConvolution
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

def raw (f : ℝ≥0 × Ω → E) (t : ℝ≥0) (p : ℝ≥0 × Ω) : E :=
  HeatVolterraKernel.raw S (ContinuousLinearMap.id ℝ E) f (t,p)

def value (f : ℝ≥0 × Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  ∫ s, raw S f t (s,ω) ∂timeMeasure H

include hS hcontr in
theorem raw_measurable (f : ℝ≥0 × Ω → E) (hf : Measurable f) (t : ℝ≥0) : Measurable (raw S f t) :=
  (HeatVolterraKernel.raw_measurable S (ContinuousLinearMap.id ℝ E) hS hcontr f hf).comp
    (measurable_const.prodMk measurable_id)

include hcontr in
theorem raw_bound (f : ℝ≥0 × Ω → E) (t : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖raw S f t p‖≤‖f p‖ := by
  unfold raw HeatVolterraKernel.raw
  split_ifs
  · exact hcontr _ _
  · simp only [norm_zero,norm_nonneg]

include hS hcontr in
theorem value_measurable (f : ℝ≥0 × Ω → E) (hf : Measurable f) (t : ℝ≥0) :
    StronglyMeasurable (value H S f t) :=
  (raw_measurable S hS hcontr f hf t).stronglyMeasurable.integral_prod_left'

theorem time_memLp (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H)) :
    ∀ᵐ ω ∂μ, MemLp (fun s => f (s,ω)) 2 (timeMeasure H) := by
  filter_upwards [hfm.norm.integrable_sq.prod_left_ae] with ω hω
  exact (memLp_two_iff_integrable_sq_norm
    ((hf.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable)).mpr hω

include hS hcontr in
theorem energy_pointwise (f : ℝ≥0 × Ω → E) (hf : Measurable f) (ω : Ω)
    (hfm : MemLp (fun s => f (s,ω)) 2 (timeMeasure H)) (t : ℝ≥0) :
    ‖value H S f t ω‖^2≤(H:ℝ)*(∫ s, ‖f (s,ω)‖^2 ∂timeMeasure H) := by
  have hr : MemLp (fun s => raw S f t (s,ω)) 2 (timeMeasure H) := by
    apply hfm.norm.mono' (((raw_measurable S hS hcontr f hf t).comp
      (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun s => raw_bound S hcontr f t (s,ω)
  have hmass : (timeMeasure H).real Set.univ=(H:ℝ) := by
    rw [Measure.real,timeMeasure_mass]
    exact ENNReal.toReal_ofReal H.property
  have hb (s : ℝ≥0) : ‖raw S f t (s,ω)‖^2≤‖f (s,ω)‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (raw_bound S hcontr f t (s,ω)) 2
  exact (IntegralEnergy.norm_integral_sq (timeMeasure H) _ hr).trans
    (by rw [hmass];exact mul_le_mul_of_nonneg_left (integral_mono hr.norm.integrable_sq hfm.norm.integrable_sq hb) H.property)

include hS hcontr in
theorem value_memLp (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H)) (t : ℝ≥0) :
    MemLp (value H S f t) 2 μ := by
  have hi := hfm.norm.integrable_sq.integral_prod_right
  apply (memLp_two_iff_integrable_sq_norm (value_measurable H S hS hcontr f hf t).aestronglyMeasurable).mpr
  apply (hi.const_mul (H:ℝ)).mono' ((value_measurable H S hS hcontr f hf t).norm.pow 2).aestronglyMeasurable
  filter_upwards [time_memLp μ H f hf hfm] with ω hω
  change ‖‖value H S f t ω‖^2‖ ≤ (H:ℝ)*(∫ s, ‖f (s,ω)‖^2 ∂timeMeasure H)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact energy_pointwise H S hS hcontr f hf ω hω t

end HeatControlConvolution
#check @HeatControlConvolution.raw_measurable
#print axioms HeatControlConvolution.raw_measurable
#check @HeatControlConvolution.raw_bound
#print axioms HeatControlConvolution.raw_bound
#check @HeatControlConvolution.value_measurable
#print axioms HeatControlConvolution.value_measurable
#check @HeatControlConvolution.time_memLp
#print axioms HeatControlConvolution.time_memLp
#check @HeatControlConvolution.energy_pointwise
#print axioms HeatControlConvolution.energy_pointwise
#check @HeatControlConvolution.value_memLp
#print axioms HeatControlConvolution.value_memLp
