import HeatForcingLp

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatForcingIdentification
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem forcing_ae (A u : Process (E := E) F μ H)
    (hu : u=A+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u)
    (V : ℝ≥0 → Lp E 2 μ) (hVs : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t)
    (G : ℝ≥0 → Ω → E) (hGm : Measurable (Function.uncurry G))
    (hVr : ∀ t, V t=ᵐ[μ] fun ω => G t ω+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) :
    A=ᵐ[energyMeasure μ H] Function.uncurry G := by
  have hAm : Measurable (A : ℝ≥0 × Ω → E) := ((Lp.stronglyMeasurable A).mono (predictable_le_product F)).measurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hGm)).mpr
  have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_add A (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u))
  rw [←hu] at hs
  filter_upwards [Measure.ae_ae_of_ae_prod hs,hVs,
    HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u] with t hs hv hc
  filter_upwards [hs,hv,hc,hVr t] with ω hs hv hc hr
  change HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω)=_ at hc
  have he := hs.symm.trans (hv.trans hr)
  change A (t,ω)+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω)=_ at he
  rw [hc] at he
  exact add_right_cancel he

end HeatForcingIdentification
#check @HeatForcingIdentification.forcing_ae
#print HeatForcingIdentification.forcing_ae
#print axioms HeatForcingIdentification.forcing_ae
