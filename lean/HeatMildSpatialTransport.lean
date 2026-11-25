import HeatMildTerminalControlMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace HeatMildSpatialTransport

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω E V : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x)) (hSc : ∀ t x, ‖S t x‖ ≤ ‖x‖)
  (T : ℝ≥0 → V →L[ℝ] V) (hT : ∀ x, Continuous (fun t => T t x)) (hTc : ∀ t x, ‖T t x‖ ≤ ‖x‖)
  (A : E →L[ℝ] V) (hA : ∀ t x, A (S t x) = T t (A x))

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
include hS hSc hA in
theorem control_value (f : ℝ≥0 × Ω → E) (hf : Measurable f)
    (hfm : MemLp f 2 (energyMeasure μ H)) (v : ℝ≥0 × Ω → V)
    (hv : v =ᵐ[energyMeasure μ H] A ∘ f) (t : ℝ≥0) :
    (fun ω => A (HeatControlConvolution.value H S f t ω)) =ᵐ[μ]
      HeatControlConvolution.value H T v t := by
  have hswap : ∀ᵐ p ∂μ.prod (timeMeasure H), v (p.2, p.1) = A (f (p.2, p.1)) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hv
  filter_upwards [HeatControlConvolution.time_memLp μ H f hf hfm, Measure.ae_ae_of_ae_prod hswap]
    with ω hω he
  let r (s : ℝ≥0) := HeatControlConvolution.raw S f t (s, ω)
  have hr : Integrable r (timeMeasure H) := by
    apply (hω.integrable one_le_two).norm.mono'
    · exact ((HeatControlConvolution.raw_measurable S hS hSc f hf t).comp
        (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable
    · exact Eventually.of_forall fun s => HeatControlConvolution.raw_bound S hSc f t (s, ω)
  change A (∫ s, r s ∂timeMeasure H) = ∫ s, HeatControlConvolution.raw T v t (s, ω) ∂timeMeasure H
  rw [← A.integral_comp_comm hr]
  apply integral_congr_ae
  filter_upwards [show (fun s => v (s, ω)) =ᵐ[timeMeasure H] fun s => A (f (s, ω)) from he] with s hs
  dsimp only [r, HeatControlConvolution.raw, HeatVolterraKernel.raw]
  by_cases ht : s < t
  · simp only [ite_eq_left ht, ContinuousLinearMap.id_apply, hs]
    exact hA (t - s) (f (s, ω))
  · simp only [ite_eq_right ht, map_zero]

omit [CompleteSpace E] [CompleteSpace V] in
include hA in
theorem slice (M : E →L[ℝ] E) (N : V →L[ℝ] V) (hM : ∀ x, A (M x) = N (A x))
    (t : ℝ≥0) (u : Process (E := E) F μ H) :
    HeatPredictableObservation.lift F μ H A (HeatVolterraSlice.slice F μ H S hS hSc M t u) =
      HeatVolterraSlice.slice F μ H T hT hTc N t (HeatPredictableObservation.lift F μ H A u) := by
  let w := HeatVolterraSlice.slice F μ H S hS hSc M t u
  let v := HeatPredictableObservation.lift F μ H A u
  let z := HeatVolterraSlice.slice F μ H T hT hTc N t v
  change HeatPredictableObservation.lift F μ H A w = z
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [HeatPredictableObservation.lift_ae F μ H A w,
    HeatPredictableObservation.lift_ae F μ H A u,
    HeatVolterraSlice.slice_ae F μ H S hS hSc M t u,
    HeatVolterraSlice.slice_ae F μ H T hT hTc N t v] with p hw hv hf hz
  change w p = _ at hf
  change z p = _ at hz
  change v p = A (u p) at hv
  rw [hw, hf, hz]
  unfold HeatVolterraKernel.raw
  by_cases ht : p.1 < t
  · rw [ite_eq_left ht, ite_eq_left ht, hv, hA, hM]
  · simp only [ite_eq_right ht, map_zero]

end HeatMildSpatialTransport

#print axioms HeatMildSpatialTransport.control_value
#print axioms HeatMildSpatialTransport.slice
