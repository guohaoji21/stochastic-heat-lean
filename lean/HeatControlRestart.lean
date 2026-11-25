import HeatControlConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatControlRestart
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

include hS hcontr in
theorem restart (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    {a b : ℝ≥0} (hab : a≤b) :
    HeatControlConvolution.value H S f b=ᵐ[μ] fun ω =>
      S (b-a) (HeatControlConvolution.value H S f a ω)+
        ∫ s in Ioc a b, S (b-s) (f (s,ω)) ∂timeMeasure H := by
  filter_upwards [HeatControlConvolution.time_memLp μ H f hf hfm] with ω hω
  have hfac (t : ℝ≥0) : Integrable (fun s => S (t-s) (f (s,ω))) (timeMeasure H) := by
    apply hω.integrable (by norm_num : (1:ENNReal)≤2) |>.norm.mono'
    · exact (((HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
        ((measurable_const.sub measurable_id).prodMk (hf.comp (measurable_id.prodMk measurable_const)))).stronglyMeasurable).aestronglyMeasurable
    · exact Eventually.of_forall (fun s => hcontr _ _)
  have hval (t : ℝ≥0) : HeatControlConvolution.value H S f t ω=
      ∫ s in Iic t, S (t-s) (f (s,ω)) ∂timeMeasure H := by
    unfold HeatControlConvolution.value HeatControlConvolution.raw HeatVolterraKernel.raw
    change (∫ s, (Iio t).indicator (fun s => S (t-s) ((ContinuousLinearMap.id ℝ E) (f (s,ω)))) s ∂timeMeasure H)=_
    rw [integral_indicator measurableSet_Iio,← integral_Iic_eq_integral_Iio]
    rfl
  rw [hval b,hval a,← Iic_union_Ioc_eq_Iic hab]
  rw [setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc (hfac b).integrableOn (hfac b).integrableOn]
  congr 1
  calc
    _ = ∫ s in Iic a, S (b-a) (S (a-s) (f (s,ω))) ∂timeMeasure H := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro s hs
      have he := congrArg (fun A : E →L[ℝ] E => A (f (s,ω))) (hsem (b-a) (a-s))
      rw [tsub_add_tsub_cancel hab hs] at he
      exact he
    _ = _ := (S (b-a)).integral_comp_comm (hfac a).integrableOn

end HeatControlRestart
#check @HeatControlRestart.restart
#print HeatControlRestart.restart
#print axioms HeatControlRestart.restart
