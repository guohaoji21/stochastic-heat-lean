import HeatGeneralContinuous
import HeatControlledFixedPoint

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatControlledContinuous
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
theorem exists_solution (hH : 0<H) (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (hlocal : StandardTerminalPastLocality J) (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 (I) B)
    (U : ℝ≥0 → Ω → E) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : E) :
    ∃ A u : Process (E := E) F μ H,
      u=HeatVolterraForcing.orbit F μ H S hS hcontr g+A+
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I) u ∧
      ∃ Y : ℝ≥0 → Ω → E, (∀ ω, Continuous (fun t => Y t ω)) ∧ StronglyAdapted F Y ∧
        StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧
        (Y 0=ᵐ[μ] fun _ => g) ∧ u=ᵐ[energyMeasure μ H] Function.uncurry Y ∧
        Integrable (fun p : ℝ≥0 × Ω => ‖Y p.1 p.2‖^2) (energyMeasure μ H) ∧
        (∀ t, t≤H → Y t=ᵐ[μ] fun ω => S t g+
          HeatControlConvolution.value H S (HeatControlAdapted.clamp U H) t ω+
          (I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) := by
  obtain ⟨A,u,hu,hunique,X,hXc,hXa,hXp,hAX,hXrep,D,hDm,hD0,hDb,hMax⟩ :=
    HeatControlledFixedPoint.exists_fixed_point F μ H S hS hcontr M hsem (I) hnull U hU hE g
  let G : ℝ≥0 → Ω → E := fun t ω => S t g+X t ω
  have hGc (ω : Ω) : Continuous (fun t => G t ω) := (hS g).add (hXc ω)
  have hGa : StronglyAdapted F G := fun t => stronglyMeasurable_const.add (hXa t)
  have hAG : HeatVolterraForcing.orbit F μ H S hS hcontr g+A=ᵐ[energyMeasure μ H] Function.uncurry G := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_add (HeatVolterraForcing.orbit F μ H S hS hcontr g) A),
      HeatVolterraForcing.orbit_ae F μ H S hS hcontr g,hAX] with p ha ho hx
    rw [ha]
    exact congrArg₂ (·+·) ho hx
  have hbound (t : ℝ≥0) (ω : Ω) : ‖G t ω‖≤‖g‖+D ω :=
    (norm_add_le _ _).trans (add_le_add (hcontr _ _) (hDb t ω))
  obtain ⟨Y,hYc,hYa,hYp,hueq,hYrep⟩ := HeatGeneralContinuous.exists_version F μ H S hS hcontr M hsem hsmooth basis J
    hH hlocal hversions hnull B hB (HeatVolterraForcing.orbit F μ H S hS hcontr g+A) u hu G hGc hGa hAG
      (fun ω => ‖g‖+D ω) ((memLp_const ‖g‖).add hDm) (fun ω => add_nonneg (norm_nonneg _) (hD0 ω)) hbound
  have hrep (t : ℝ≥0) (ht : t≤H) : Y t=ᵐ[μ] fun ω => S t g+
      HeatControlConvolution.value H S (HeatControlAdapted.clamp U H) t ω+
      (I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω := by
    filter_upwards [hYrep t ht,hXrep t] with ω hy hx
    exact hy.trans (congrArg (fun z => S t g+z+(I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) hx)
  have h0 : Y 0=ᵐ[μ] fun _ => g := by
    have he := hrep 0 zero_le
    rw [HeatMildSolution.slice_zero F μ H S hS hcontr M u,map_zero,hzero] at he
    filter_upwards [he,Lp.coeFn_zero E 2 μ] with ω hy hz
    rw [hy,hz]
    simp only [ContinuousLinearMap.id_apply,HeatControlConvolution.value,HeatControlConvolution.raw,
      HeatVolterraKernel.raw,not_lt_zero,ite_false,integral_zero,Pi.zero_apply,add_zero]
  have henergy := ((memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq).congr
    (hueq.fun_comp (fun z : E => ‖z‖^2))
  exact ⟨A,u,hu,Y,hYc,hYa,hYp,h0,hueq,henergy,hrep⟩

end HeatControlledContinuous
#check @HeatControlledContinuous.exists_solution
#print HeatControlledContinuous.exists_solution
#print axioms HeatControlledContinuous.exists_solution
