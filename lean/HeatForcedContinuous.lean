import HeatForcedMoment
import HeatConvolutionContinuous

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatForcedContinuous
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : E,
    ‖S δ (S τ x)-S τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

include hsmooth in
theorem exists_solution (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B)
    (A : Process (E := E) F μ H) (R : ℝ) (hR : 0≤R) (hA : A∈HeatMomentBall.Ball R)
    (G : ℝ≥0 → Ω → E) (hGc : ∀ ω, Continuous (fun t => G t ω)) (hGa : StronglyAdapted F G)
    (hAG : A=ᵐ[energyMeasure μ H] Function.uncurry G) :
    ∃ u : Process (E := E) F μ H, u=A+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      ∃ Y : ℝ≥0 → Ω → E, (∀ ω, Continuous (fun t => Y t ω)) ∧ StronglyAdapted F Y ∧
        StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧
        u=ᵐ[energyMeasure μ H] Function.uncurry Y ∧
        (∀ t, t≤H → Y t=ᵐ[μ] fun ω => G t ω+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) := by
  obtain ⟨u,hu,K,hK,hm⟩ := HeatForcedMoment.exists_uniform F μ H S hS hcontr M hsem I B hB A R hR hA
  obtain ⟨Z,hZc,hZa,hZ⟩ := HeatConvolutionContinuous.exists_version F μ H S hS hcontr M hsem hsmooth I hH hn B hB u K hK hm
  let Y := fun t ω => G t ω+Z t ω
  have hYc (ω : Ω) : Continuous (fun t => Y t ω) := (hGc ω).add (hZc ω)
  have hYa : StronglyAdapted F Y := fun t => (hGa t).add (hZa t)
  have hYp := SHE.ContinuousPredictable.stronglyMeasurable F Y hYa hYc
  have hrep (t : ℝ≥0) (ht : t≤H) : Y t=ᵐ[μ] fun ω => G t ω+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω := by
    filter_upwards [hZ t ht] with ω hz
    exact congrArg (fun z => G t ω+z) hz
  have hueq : u=ᵐ[energyMeasure μ H] Function.uncurry Y := by
    have huM : Measurable (u : ℝ≥0 × Ω → E) := ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
    have hYM : Measurable (Function.uncurry Y) := (hYp.mono (predictable_le_product F)).measurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun huM hYM)).mpr
    have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_add A (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u))
    rw [←hu] at hs
    filter_upwards [Measure.ae_ae_of_ae_prod hs,Measure.ae_ae_of_ae_prod hAG,
      HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u,timeMeasure_ae_mem H] with t hs ha hc ht
    change (fun ω => HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω))=ᵐ[μ] _ at hc
    filter_upwards [hs,ha,hc,hZ t ht.2] with ω hs ha hc hz
    change u (t,ω)=G t ω+Z t ω
    rw [hs]
    change A (t,ω)+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω)=_
    rw [ha,hc,hz]
    rfl
  exact ⟨u,hu,Y,hYc,hYa,hYp,hueq,hrep⟩

end HeatForcedContinuous
#check @HeatForcedContinuous.exists_solution
#print HeatForcedContinuous.exists_solution
#print axioms HeatForcedContinuous.exists_solution
