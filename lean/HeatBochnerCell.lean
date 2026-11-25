import HeatControlConvolution
import SHE.IntervalTimeMeasure

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatBochnerCell
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def value (f : ℝ≥0 × Ω → E) (a b : ℝ≥0) (ω : Ω) : E := ∫ s in Ioc a b, f (s,ω) ∂timeMeasure H

theorem square_integrable (f : ℝ≥0 × Ω → E) (hf : Measurable f)
    (hfm : MemLp f 2 (energyMeasure μ H)) (a b : ℝ≥0) : MemLp (value H f a b) 2 μ := by
  let ν := (timeMeasure H).restrict (Ioc a b)
  let Q : Ω → ℝ := fun ω => ∫ s,‖f (s,ω)‖^2 ∂ν
  have hFi : Integrable (fun p : ℝ≥0 × Ω => (Ioc a b).indicator (fun s => ‖f (s,p.2)‖^2) p.1) (energyMeasure μ H) := by
    exact hfm.norm.integrable_sq.indicator ((measurableSet_Ioc).preimage measurable_fst)
  have hQi : Integrable Q μ := by
    convert hFi.integral_prod_right using 1
    funext ω
    exact (integral_indicator measurableSet_Ioc).symm
  letI : SFinite (timeMeasure H) := inferInstance
  have hm : StronglyMeasurable (value H f a b) := by
    have hh := hf.stronglyMeasurable.indicator ((measurableSet_Ioc : MeasurableSet (Ioc a b)).preimage measurable_fst)
    have heq : (fun ω => ∫ s, ((Prod.fst ⁻¹' Ioc a b).indicator f) (s,ω) ∂timeMeasure H)=value H f a b := by
      funext ω
      exact integral_indicator measurableSet_Ioc
    rw [←heq]
    exact hh.integral_prod_left'
  have hbound : ∀ᵐ ω ∂μ, ‖value H f a b ω‖^2≤ν.real univ*Q ω := by
    filter_upwards [HeatControlConvolution.time_memLp μ H f hf hfm] with ω hω
    exact IntegralEnergy.norm_integral_sq ν _ (hω.restrict (Ioc a b))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (hQi.const_mul (ν.real univ)).mono' (hm.norm.pow 2).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  change ‖‖value H f a b ω‖^2‖≤_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hω

theorem energy (f : ℝ≥0 × Ω → E) (hf : Measurable f)
    (hfm : MemLp f 2 (energyMeasure μ H)) (a b : ℝ≥0) :
    ‖(square_integrable μ H f hf hfm a b).toLp (value H f a b)‖^2≤
      ((timeMeasure H).restrict (Ioc a b)).real univ*
      (∫ p, (Ioc a b).indicator (fun s => ‖f (s,p.2)‖^2) p.1 ∂energyMeasure μ H) := by
  let ν := (timeMeasure H).restrict (Ioc a b)
  let Q : Ω → ℝ := fun ω => ∫ s,‖f (s,ω)‖^2 ∂ν
  have hFi : Integrable (fun p : ℝ≥0 × Ω => (Ioc a b).indicator (fun s => ‖f (s,p.2)‖^2) p.1) (energyMeasure μ H) :=
    hfm.norm.integrable_sq.indicator ((measurableSet_Ioc).preimage measurable_fst)
  have hQi : Integrable Q μ := by
    convert hFi.integral_prod_right using 1
    funext ω
    exact (integral_indicator measurableSet_Ioc).symm
  have hFubini : (∫ p, (Ioc a b).indicator (fun s => ‖f (s,p.2)‖^2) p.1 ∂energyMeasure μ H)=∫ ω,Q ω ∂μ := by
    change (∫ p, (Ioc a b).indicator (fun s => ‖f (s,p.2)‖^2) p.1 ∂(timeMeasure H).prod μ)=_
    rw [integral_prod_symm _ hFi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => integral_indicator measurableSet_Ioc)
  rw [hFubini,←integral_const_mul,realLp_norm_sq]
  apply integral_mono_ae (Lp.memLp _).norm.integrable_sq (hQi.const_mul (ν.real univ))
  filter_upwards [(square_integrable μ H f hf hfm a b).coeFn_toLp,
    HeatControlConvolution.time_memLp μ H f hf hfm] with ω hd hω
  rw [hd]
  exact IntegralEnergy.norm_integral_sq ν _ (hω.restrict (Ioc a b))

end HeatBochnerCell
#check @HeatBochnerCell.square_integrable
#print axioms HeatBochnerCell.square_integrable
#check @HeatBochnerCell.energy
#print HeatBochnerCell.energy
#print axioms HeatBochnerCell.energy
