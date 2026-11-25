import HeatConvolutionTimeMoment
import SHEStochastic.ScalarLipschitzContinuousVersion

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatConvolutionContinuous
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : E,
    ‖S δ (S τ x)-S τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

include hS hcontr hsem hsmooth in
theorem exists_version (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B)
    (u : Process (E := E) F μ H) (R : ℝ) (hR : 0≤R) (hu : u∈HeatMomentBall.Ball R) :
    ∃ Z : ℝ≥0 → Ω → E, (∀ ω, Continuous (fun t => Z t ω)) ∧ StronglyAdapted F Z ∧
      ∀ t, t≤H → Z t =ᵐ[μ] I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) := by
  have ha (t : ℝ≥0) : StronglyMeasurable[F t]
      (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) : Ω → E) := by
    obtain ⟨A,hA,hrep⟩ := I.adapted t (HeatVolterraSlice.slice F μ H S hS hcontr M t u)
      (StoppedItoInputs.stop_stopped F μ H t _)
    exact NullCompleteFiltration.stronglyMeasurable_congr F μ hn t hA hrep
  apply SHEStochastic.ScalarLipschitzContinuousVersion.exists_version hH hn
    (fun t _ => I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u))
    (fun t _ => ha t) (HeatConvolutionTimeMoment.coefficient H M B R) (by unfold HeatConvolutionTimeMoment.coefficient;positivity)
  intro s t hs ht
  rcases le_total s t with hst | hts
  · simpa only [HeatMomentBall.moment,SHEStochastic.ScalarLipschitzItoMoment.moment,norm_sub_rev,sub_sq_comm] using
      HeatConvolutionTimeMoment.increment F μ H S hS hcontr M hsem hsmooth I B hB u R hR hu hst ht
  · simpa only [HeatMomentBall.moment,SHEStochastic.ScalarLipschitzItoMoment.moment] using
      HeatConvolutionTimeMoment.increment F μ H S hS hcontr M hsem hsmooth I B hB u R hR hu hts hs

end HeatConvolutionContinuous
#check @HeatConvolutionContinuous.exists_version
#print axioms HeatConvolutionContinuous.exists_version
