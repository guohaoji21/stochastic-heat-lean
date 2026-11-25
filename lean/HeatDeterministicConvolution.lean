import HeatVolterraModel
import SHE.IntegralEnergy
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatDeterministicConvolution
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

def raw (f : Process (E := E) F μ H) (t : ℝ≥0) (p : ℝ≥0 × Ω) : E :=
  HeatVolterraKernel.raw S (ContinuousLinearMap.id ℝ E) f (t,p)

def value (f : Process (E := E) F μ H) (t : ℝ≥0) (ω : Ω) : E :=
  ∫ s, raw F μ H S f t (s,ω) ∂timeMeasure H

include hS hcontr in
theorem raw_measurable (f : Process (E := E) F μ H) (t : ℝ≥0) : Measurable (raw F μ H S f t) := by
  have hm := HeatVolterraKernel.raw_measurable S (ContinuousLinearMap.id ℝ E) hS hcontr f
    (HeatVolterraModel.state_measurable F μ H S hS hcontr f)
  exact hm.comp (measurable_const.prodMk measurable_id)

include hcontr in
theorem raw_bound (f : Process (E := E) F μ H) (t : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖raw F μ H S f t p‖≤‖f p‖ := by
  unfold raw HeatVolterraKernel.raw
  split_ifs
  · exact hcontr _ _
  · simp only [norm_zero,norm_nonneg]

include hS hcontr in
theorem value_measurable (f : Process (E := E) F μ H) (t : ℝ≥0) :
    StronglyMeasurable (value F μ H S f t) :=
  (raw_measurable F μ H S hS hcontr f t).stronglyMeasurable.integral_prod_left'

include hS hcontr in
theorem time_memLp (f : Process (E := E) F μ H) :
    ∀ᵐ ω ∂μ, MemLp (fun s => f (s,ω)) 2 (timeMeasure H) := by
  have hm : Measurable (f : ℝ≥0 × Ω → E) :=
    ((Lp.stronglyMeasurable f).mono (predictable_le_product F)).measurable
  have hi := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp f)).norm.integrable_sq.prod_left_ae
  filter_upwards [hi] with ω hω
  apply (memLp_two_iff_integrable_sq_norm
    ((hm.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable)).mpr
  exact hω

include hS hcontr in
theorem energy_pointwise (f : Process (E := E) F μ H) (ω : Ω)
    (hf : MemLp (fun s => f (s,ω)) 2 (timeMeasure H)) (t : ℝ≥0) :
    ‖value F μ H S f t ω‖^2≤(H:ℝ)*(∫ s, ‖f (s,ω)‖^2 ∂timeMeasure H) := by
  have hr : MemLp (fun s => raw F μ H S f t (s,ω)) 2 (timeMeasure H) := by
    apply hf.norm.mono' (((raw_measurable F μ H S hS hcontr f t).comp
      (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun s => raw_bound F μ H S hcontr f t (s,ω)
  have hmass : (timeMeasure H).real Set.univ=(H:ℝ) := by
    rw [Measure.real,timeMeasure_mass]
    exact ENNReal.toReal_ofReal H.property
  have hb (s : ℝ≥0) : ‖raw F μ H S f t (s,ω)‖^2≤‖f (s,ω)‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (raw_bound F μ H S hcontr f t (s,ω)) 2
  exact (IntegralEnergy.norm_integral_sq (timeMeasure H) _ hr).trans
    (by rw [hmass];exact mul_le_mul_of_nonneg_left (integral_mono hr.norm.integrable_sq hf.norm.integrable_sq hb) H.property)

include hS hcontr in
theorem value_memLp (f : Process (E := E) F μ H) (t : ℝ≥0) : MemLp (value F μ H S f t) 2 μ := by
  have hi := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp f)).norm.integrable_sq.integral_prod_right
  apply (memLp_two_iff_integrable_sq_norm (value_measurable F μ H S hS hcontr f t).aestronglyMeasurable).mpr
  apply (hi.const_mul (H:ℝ)).mono' ((value_measurable F μ H S hS hcontr f t).norm.pow 2).aestronglyMeasurable
  filter_upwards [time_memLp F μ H S hS hcontr f] with ω hω
  change ‖‖value F μ H S f t ω‖^2‖ ≤ (H:ℝ)*(∫ s, ‖f (s,ω)‖^2 ∂timeMeasure H)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact energy_pointwise F μ H S hS hcontr f ω hω t

end HeatDeterministicConvolution
#check @HeatDeterministicConvolution.raw_measurable
#print axioms HeatDeterministicConvolution.raw_measurable
#check @HeatDeterministicConvolution.raw_bound
#print axioms HeatDeterministicConvolution.raw_bound
#check @HeatDeterministicConvolution.value_measurable
#print axioms HeatDeterministicConvolution.value_measurable
#check @HeatDeterministicConvolution.time_memLp
#print axioms HeatDeterministicConvolution.time_memLp
#check @HeatDeterministicConvolution.energy_pointwise
#print axioms HeatDeterministicConvolution.energy_pointwise
#check @HeatDeterministicConvolution.value_memLp
#print axioms HeatDeterministicConvolution.value_memLp
