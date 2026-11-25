import HeatLocalUniqueness
import HeatForcedContinuous
import HeatBoundedForcing
import SHEStochastic.ScalarPredictableNormStop
import SHEStochastic.ContinuousNormExit

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatLocalizedContinuous
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
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
theorem exists_versions (hH : 0<H) (hlocal : StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 (I) B)
    (A u : Process (E := E) F μ H)
    (hu : u=A+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I) u)
    (G : ℝ≥0 → Ω → E) (hGc : ∀ ω, Continuous (fun t => G t ω)) (hGa : StronglyAdapted F G)
    (hAG : A=ᵐ[energyMeasure μ H] Function.uncurry G) :
    ∀ N : ℕ, ∃ Y : ℝ≥0 → Ω → E,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ StronglyAdapted F Y ∧
      ∀ t, t≤H → ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0)<SHEStochastic.ContinuousNormExit.exit G N ω →
        Y t ω=G t ω+(I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω := by
  intro N
  let GN : ℝ≥0 → Ω → E := fun t ω => SHEStochastic.BallProjection.project (N:ℝ≥0) (G t ω)
  have hGNc (ω : Ω) : Continuous (fun t => GN t ω) :=
    (SHEStochastic.BallProjection.lipschitz (N:ℝ≥0)).continuous.comp (hGc ω)
  have hGNa : StronglyAdapted F GN := fun t =>
    (SHEStochastic.BallProjection.lipschitz (N:ℝ≥0)).continuous.comp_stronglyMeasurable (hGa t)
  have hGNp := SHE.ContinuousPredictable.stronglyMeasurable F GN hGNa hGNc
  obtain ⟨AN,hAN,hANball⟩ := HeatBoundedForcing.bounded_process F μ H GN hGNp N (Nat.cast_nonneg N)
    (fun t ω => SHEStochastic.BallProjection.norm_le_radius (N:ℝ≥0) (G t ω))
  obtain ⟨uN,huN,Y,hYc,hYa,hYp,huNY,hYrep⟩ :=
    HeatForcedContinuous.exists_solution F μ H S hS hcontr M hsem hsmooth (I) hH hnull B hB
      AN ((N:ℝ)^16) (by positivity) hANball GN hGNc hGNa hAN
  let τ := SHEStochastic.ContinuousNormExit.exit G N
  have hτ : IsStoppingTime F τ := SHEStochastic.ContinuousNormExit.isStoppingTime G hGc F hGa N
  have hGp := SHE.ContinuousPredictable.stronglyMeasurable F G hGa hGc
  have hpre : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0)<τ p.2} :=
    SHEStochastic.ScalarPredictableNormStop.predictable F G hGp hGc N
  have hforcing : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 → AN p=A p := by
    filter_upwards [hAN,hAG] with p hn ha ht
    rw [hn,ha]
    exact SHEStochastic.BallProjection.of_norm_le (N:ℝ≥0)
      (SHEStochastic.ContinuousNormExit.before_bound G hGc N p.1 p.2 ht).le
  have hinput := HeatLocalUniqueness.unique_before F μ H S hS hcontr M hsem basis J
    hlocal hversions hnull τ hτ hpre AN A uN u huN hu hforcing
  refine ⟨Y,hYc,hYa,?_⟩
  intro t ht
  have hi := HeatConvolutionStopLocality.integral_eq_before F μ H S hS hcontr M basis J
    hlocal hversions hnull uN u t τ hτ hinput
  filter_upwards [hYrep t ht,hi] with ω hy hi hbefore
  rw [hy,hi hbefore.le]
  change SHEStochastic.BallProjection.project (N:ℝ≥0) (G t ω)+_=G t ω+_
  rw [SHEStochastic.BallProjection.of_norm_le (N:ℝ≥0)
    (SHEStochastic.ContinuousNormExit.before_bound G hGc N t ω hbefore).le]

end HeatLocalizedContinuous
#check @HeatLocalizedContinuous.exists_versions
#print HeatLocalizedContinuous.exists_versions
#print axioms HeatLocalizedContinuous.exists_versions
