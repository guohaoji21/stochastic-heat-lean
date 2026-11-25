import HeatMomentSolution
import HeatConvolutionContinuous

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatContinuousMild
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
theorem exists_solution (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (hzero : S 0=ContinuousLinearMap.id ℝ E) (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B) (g : E) :
    ∃ u : Process (E := E) F μ H,
      u=HeatVolterraForcing.orbit F μ H S hS hcontr g+
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      ∃ Y : ℝ≥0 → Ω → E, (∀ ω, Continuous (fun t => Y t ω)) ∧ StronglyAdapted F Y ∧
        StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧
        (Y 0=ᵐ[μ] (fun _ => g)) ∧
        (u=ᵐ[energyMeasure μ H] Function.uncurry Y) ∧
        Integrable (fun p : ℝ≥0 × Ω => ‖Y p.1 p.2‖^2) (energyMeasure μ H) ∧
        (∀ t, t≤H → Y t=ᵐ[μ] HeatMildSolution.value F μ H S hS hcontr M I g u t) := by
  obtain ⟨u,hu,R,hR,hm⟩ := HeatMomentSolution.exists_uniform F μ H S hS hcontr M hsem I B hB g
  obtain ⟨Z,hZc,hZa,hZ⟩ := HeatConvolutionContinuous.exists_version F μ H S hS hcontr M hsem hsmooth I
    hH hn B hB u R hR hm
  let Y : ℝ≥0 → Ω → E := fun t ω => S t g+Z t ω
  have hYc (ω : Ω) : Continuous (fun t => Y t ω) := (hS g).add (hZc ω)
  have hYa : StronglyAdapted F Y := fun t => stronglyMeasurable_const.add (hZa t)
  have hYp : StronglyMeasurable[F.predictable] (Function.uncurry Y) :=
    SHE.ContinuousPredictable.stronglyMeasurable F Y hYa hYc
  have hrep (t : ℝ≥0) (ht : t≤H) : Y t=ᵐ[μ] HeatMildSolution.value F μ H S hS hcontr M I g u t := by
    filter_upwards [hZ t ht,Lp.coeFn_add (Lp.const 2 μ (S t g))
      (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)),Lp.coeFn_const 2 μ (S t g)] with ω hz ha hc
    change S t g+Z t ω=(Lp.const 2 μ (S t g)+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)) ω
    rw [ha]
    simp only [Pi.add_apply,hc,Function.const_apply,hz]
  have h0 : Y 0=ᵐ[μ] (fun _ => g) := by
    have hh := hrep 0 zero_le
    rw [HeatMildSolution.initial_value F μ H S hS hcontr M I hzero g u] at hh
    exact hh.trans (Lp.coeFn_const 2 μ g)
  have hueq : u=ᵐ[energyMeasure μ H] Function.uncurry Y := by
    have huM : Measurable (u : ℝ≥0 × Ω → E) := ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
    have hYM : Measurable (Function.uncurry Y) := (hYp.mono (predictable_le_product F)).measurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun huM hYM)).mpr
    filter_upwards [HeatMildSolution.value_slices F μ H S hS hcontr M I hsem g u hu,
      timeMeasure_ae_mem H] with t ht htime
    exact ht.trans (hrep t htime.2).symm
  have henergy := ((memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq).congr
    (hueq.fun_comp (fun z : E => ‖z‖^2))
  exact ⟨u,hu,Y,hYc,hYa,hYp,h0,hueq,henergy,hrep⟩

end HeatContinuousMild
#check @HeatContinuousMild.exists_solution
#print axioms HeatContinuousMild.exists_solution
