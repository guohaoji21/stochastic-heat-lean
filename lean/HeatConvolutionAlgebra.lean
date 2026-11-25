import HeatVolterraFixedPoint
import HeatVolterraContinuity

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatConvolutionAlgebra
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)

theorem slice_sub (u v : Process (E := E) F μ H) (t : ℝ≥0) :
    HeatVolterraSlice.slice F μ H S hS hcontr M t (u-v)=
      HeatVolterraSlice.slice F μ H S hS hcontr M t u-HeatVolterraSlice.slice F μ H S hS hcontr M t v := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [HeatVolterraSlice.slice_ae F μ H S hS hcontr M t (u-v),
    HeatVolterraSlice.slice_ae F μ H S hS hcontr M t u,HeatVolterraSlice.slice_ae F μ H S hS hcontr M t v,
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v),ae_eq_of_ae_eq_trim (Lp.coeFn_sub
      (HeatVolterraSlice.slice F μ H S hS hcontr M t u) (HeatVolterraSlice.slice F μ H S hS hcontr M t v))] with p hd hu hv hi ho
  rw [hd,ho]
  simp only [Pi.sub_apply]
  rw [hu,hv]
  simp only [HeatVolterraKernel.raw]
  split_ifs
  · rw [hi]
    simp only [Pi.sub_apply,map_sub]
  · exact (sub_self 0).symm

theorem sub (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (I : StandardTerminalIto (C := E) (E := E) F μ H) (u v : Process (E := E) F μ H) :
    HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I (u-v)=
      HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u-
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I v := by
  let N := HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I
  apply PastItoAlgebra.eq_of_ambient_ae
  have hm (w : Process (E := E) F μ H) : Measurable (fun p : ℝ≥0 × Ω => w p) :=
    ((Lp.stronglyMeasurable w).mono (predictable_le_product F)).measurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hm (N (u-v))) (hm (N u-N v)))).mpr
  filter_upwards [HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem (u-v),
    HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u,
    HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem v,
    Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub (N u) (N v)))] with t hd hu hv ho
  rw [slice_sub F μ H S hS hcontr M u v t,map_sub] at hd
  filter_upwards [hd,hu,hv,ho,Lp.coeFn_sub (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u))
    (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t v))] with ω hd hu hv ho hsub
  change N u (t,ω)=_ at hu
  change N v (t,ω)=_ at hv
  apply hd.trans
  rw [hsub,ho]
  simp only [Pi.sub_apply]
  rw [hu,hv]

theorem zero (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (I : StandardTerminalIto (C := E) (E := E) F μ H) :
    HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I 0=0 := by
  simpa only [sub_self] using sub F μ H S hS hcontr M hsem I 0 0

end HeatConvolutionAlgebra
#check @HeatConvolutionAlgebra.slice_sub
#print axioms HeatConvolutionAlgebra.slice_sub
#check @HeatConvolutionAlgebra.sub
#print axioms HeatConvolutionAlgebra.sub
#check @HeatConvolutionAlgebra.zero
#print HeatConvolutionAlgebra.zero
#print axioms HeatConvolutionAlgebra.zero
