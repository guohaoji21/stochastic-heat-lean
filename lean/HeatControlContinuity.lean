import HeatControlConvolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatControlContinuity
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatControlConvolution
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

include hS in
theorem raw_continuousAt (f : ℝ≥0 × Ω → E) (ω : Ω) (t s : ℝ≥0) (hst : s≠t) :
    ContinuousAt (fun a => raw S f a (s,ω)) t := by
  rcases lt_or_gt_of_ne hst with hst | hts
  · have hc : Continuous (fun a : ℝ≥0 => S (a-s) (f (s,ω))) :=
      (hS _).comp (continuous_id.sub continuous_const)
    have he : (fun a => raw S f a (s,ω)) =ᶠ[𝓝 t] (fun a => S (a-s) (f (s,ω))) := by
      filter_upwards [Ioi_mem_nhds hst] with a ha
      change s<a at ha
      simp only [raw,HeatVolterraKernel.raw,if_pos ha,ContinuousLinearMap.id_apply]
    change Tendsto (fun a => raw S f a (s,ω)) (𝓝 t) (𝓝 (raw S f t (s,ω)))
    rw [show raw S f t (s,ω)=S (t-s) (f (s,ω)) by simp only [raw,HeatVolterraKernel.raw,if_pos hst,ContinuousLinearMap.id_apply]]
    exact hc.continuousAt.tendsto.congr' he.symm
  · have he : (fun a => raw S f a (s,ω)) =ᶠ[𝓝 t] (fun _ => (0:E)) := by
      filter_upwards [Iio_mem_nhds hts] with a ha
      change a<s at ha
      simp only [raw,HeatVolterraKernel.raw,if_neg (not_lt_of_ge ha.le)]
    change Tendsto (fun a => raw S f a (s,ω)) (𝓝 t) (𝓝 (raw S f t (s,ω)))
    rw [show raw S f t (s,ω)=0 by simp only [raw,HeatVolterraKernel.raw,if_neg (not_lt_of_ge hts.le)]]
    exact tendsto_const_nhds.congr' he.symm

include hS hcontr in
theorem continuous_path (f : ℝ≥0 × Ω → E) (hfm : Measurable f) (ω : Ω)
    (hf : MemLp (fun s => f (s,ω)) 2 (timeMeasure H)) :
    Continuous (fun t => value H S f t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_integral_filter_of_dominated_convergence (fun s => ‖f (s,ω)‖)
    (Filter.Eventually.of_forall (fun a => ((raw_measurable S hS hcontr f hfm a).comp
      (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun a => Filter.Eventually.of_forall (fun s => raw_bound S hcontr f a (s,ω))))
    (hf.integrable one_le_two).norm
    (((timeMeasure H).ae_ne t).mono (fun s hs => (raw_continuousAt S hS f ω t s hs).tendsto))

end HeatControlContinuity
#check @HeatControlContinuity.raw_continuousAt
#print axioms HeatControlContinuity.raw_continuousAt
#check @HeatControlContinuity.continuous_path
#print axioms HeatControlContinuity.continuous_path
