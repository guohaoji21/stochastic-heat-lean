import HeatConvolutionAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatSliceNorm
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)

theorem bound (u : Process (E := E) F μ H) (t : ℝ≥0) :
    ‖HeatVolterraSlice.slice F μ H S hS hcontr M t u‖≤‖M‖*‖u‖ := by
  have hh : ‖HeatVolterraSlice.slice F μ H S hS hcontr M t u‖≤‖(‖M‖:ℝ) • u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    have hr := ae_eq_of_ae_eq_trim (Lp.coeFn_smul ‖M‖ u)
    have hs := HeatVolterraSlice.slice_ae F μ H S hS hcontr M t u
    have hb : ∀ᵐ p ∂energyMeasure μ H,
        ‖HeatVolterraSlice.slice F μ H S hS hcontr M t u p‖≤‖((‖M‖:ℝ) • u) p‖ := by
      filter_upwards [hr,hs] with p hr hs
      rw [hs,hr,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg M)]
      exact HeatVolterraModel.raw_norm_bound F μ H S hS hcontr M u (t,p)
    have hm : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω |
        ¬‖HeatVolterraSlice.slice F μ H S hS hcontr M t u p‖≤‖((‖M‖:ℝ) • u) p‖} :=
      (measurableSet_le (Lp.stronglyMeasurable (HeatVolterraSlice.slice F μ H S hS hcontr M t u)).norm.measurable
        (Lp.stronglyMeasurable ((‖M‖:ℝ) • u)).norm.measurable).compl
    rw [ae_iff,trim_measurableSet_eq (predictable_le_product F) hm]
    exact ae_iff.mp hb
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg M)] using hh

theorem integrable (u : Process (E := E) F μ H) (T : ℝ≥0) :
    Integrable (fun t => HeatVolterraSlice.slice F μ H S hS hcontr M t u) (timeMeasure T) :=
  (integrable_const (‖M‖*‖u‖)).mono'
    (HeatVolterraContinuity.slice_continuous F μ H S hS hcontr M u).aestronglyMeasurable
    (Eventually.of_forall (bound F μ H S hS hcontr M u))

end HeatSliceNorm
#check @HeatSliceNorm.bound
#print axioms HeatSliceNorm.bound
#check @HeatSliceNorm.integrable
#print HeatSliceNorm.integrable
#print axioms HeatSliceNorm.integrable
