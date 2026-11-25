import HeatLocalizedContinuous
import HeatContinuousLocalization
import HeatForcingLp

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatGeneralContinuous
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nontrivial E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : E,
    ‖S δ (S τ x)-S τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

include hsmooth in
theorem exists_version (hH : 0<H) (hlocal : StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 (I) B)
    (A u : Process (E := E) F μ H)
    (hu : u=A+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I) u)
    (G : ℝ≥0 → Ω → E) (hGc : ∀ ω, Continuous (fun t => G t ω)) (hGa : StronglyAdapted F G)
    (hAG : A=ᵐ[energyMeasure μ H] Function.uncurry G)
    (D : Ω → ℝ) (hDm : MemLp D 2 μ) (hD0 : ∀ ω, 0≤D ω) (hDb : ∀ t ω, ‖G t ω‖≤D ω) :
    ∃ Y : ℝ≥0 → Ω → E, (∀ ω, Continuous (fun t => Y t ω)) ∧ StronglyAdapted F Y ∧
      StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧
      u=ᵐ[energyMeasure μ H] Function.uncurry Y ∧
      (∀ t, t≤H → Y t=ᵐ[μ] fun ω => G t ω+(I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) := by
  obtain ⟨V,hVc,hVa,hsl,hrep⟩ := HeatForcingLp.exists_family F μ H S hS hcontr M hsem (I)
    A u hu G hGc hGa hAG D hDm hD0 hDb
  have hl := HeatLocalizedContinuous.exists_versions F μ H S hS hcontr M hsem hsmooth basis J
    hH hlocal hversions hnull B hB A u hu G hGc hGa hAG
  choose Y hYc hYa hYrep using hl
  have hloc (n : ℕ) (t : ℝ≥0) (ht : t≤H) : ∀ᵐ ω ∂μ,
      (t : WithTop ℝ≥0)<SHEStochastic.ContinuousNormExit.exit G n ω → Y n t ω=V t ω := by
    filter_upwards [hYrep n t ht,hrep t] with ω hy hv htau
    exact (hy htau).trans hv.symm
  obtain ⟨Z,hZc,hZa,hZp,hZrep⟩ := HeatContinuousLocalization.exists_version F μ H hnull
    G hGc D (fun t ω _ => hDb t ω) V hVa Y hYc hloc
  have henergy : u=ᵐ[energyMeasure μ H] Function.uncurry Z := by
    have hum : Measurable (u : ℝ≥0 × Ω → E) := ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
    have hzm := (hZp.mono (predictable_le_product F)).measurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hum hzm)).mpr
    filter_upwards [hsl,timeMeasure_ae_mem H] with t hsl ht
    exact hsl.trans (hZrep t ht.2).symm
  exact ⟨Z,hZc,hZa,hZp,henergy,fun t ht => (hZrep t ht).trans (hrep t)⟩

end HeatGeneralContinuous
#check @HeatGeneralContinuous.exists_version
#print HeatGeneralContinuous.exists_version
#print axioms HeatGeneralContinuous.exists_version
