import HeatScalarWeakMaximum
import HeatWeakPathScalarEquation
import HeatScalarMartingaleEnvelope
import HeatFourierFrameMeasure

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatModalWeakMaximum
open MeasureTheory Filter SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatWeakDirichlet HeatFourierFrame
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

theorem exists_envelope (hlocal : SHE.StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ) (n : ℤ) :
    ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω,0≤D ω) ∧
      (∫ ω,(D ω)^2 ∂μ)≤4*‖HeatHilbertRandomStop.project F μ H (coordinate n) (HeatWeakStochasticInput.noise F μ H M sol.input)‖^2 ∧
      (∀ᵐ ω ∂μ, ∀ t, t≤H → |coordinate n (sol.path t ω)|≤
        2*(|coordinate n g|+HeatScalarControlBound.bound H (fun p => coordinate n (HeatControlAdapted.clamp U H p)) ω+D ω)) := by
  let h := HeatWeakStochasticInput.noise F μ H M sol.input
  let q := HeatHilbertRandomStop.project F μ H (coordinate n) h
  obtain ⟨N,D,hNc,hNa,hNr,hD,hD0,hNb,hDe⟩ := HeatScalarMartingaleEnvelope.exists_envelope F μ H J hlocal hversions hnull q
  refine ⟨D,hD,hD0,hDe,?_⟩
  let f := fun p => coordinate n (HeatControlAdapted.clamp U H p)
  have hf : Measurable f := (coordinate n).continuous.measurable.comp (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm : MemLp f 2 (energyMeasure μ H) := (coordinate n).comp_memLp' (HeatClampedControl.square_integrable F μ H U hU hE)
  apply HeatScalarWeakMaximum.bound μ H (fun t ω => coordinate n (sol.path t ω)) N D (coordinate n g) (rate n)
    (rate_nonnegative n) (fun ω => (coordinate n).continuous.comp (sol.path_continuous ω)) hD0 hNb f hf hfm
  intro t ht
  have hw := HeatWeakPathScalarEquation.equation F μ H M (HeatTerminalNaturality.integral F μ H basis J)
    U hU hE g sol ht (vector n) (-(rate n) • vector n) (eigen n)
  have hp := HeatHilbertRandomStop.integral_projection F μ H basis J (coordinate n) (SHE.StoppedItoInputs.stop F μ H t h)
  rw [HeatHilbertRandomStop.project_stop] at hp
  have hn : N t=ᵐ[μ] J.integral (SHE.StoppedItoInputs.stop F μ H t q) := hNr t
  filter_upwards [hw,hp,hn] with ω hw hp hn
  change inner ℝ (vector n) (sol.path t ω)=inner ℝ (vector n) g+
    (∫ s,inner ℝ (vector n) (HeatControlAdapted.clamp U H (s,ω)) ∂timeMeasure t)+
    (∫ s,inner ℝ (-(rate n) • vector n) (sol.path s ω) ∂timeMeasure t)+
    coordinate n ((HeatTerminalNaturality.integral F μ H basis J).integral (SHE.StoppedItoInputs.stop F μ H t h) ω) at hw
  simp_rw [real_inner_smul_left] at hw
  rw [integral_const_mul] at hw
  rw [←hn] at hp
  change coordinate n (sol.path t ω)+rate n*(∫ s,coordinate n (sol.path s ω) ∂timeMeasure t)=
    coordinate n g+(∫ s,coordinate n (HeatControlAdapted.clamp U H (s,ω)) ∂timeMeasure t)+N t ω
  change inner ℝ (vector n) (sol.path t ω)+rate n*(∫ s,inner ℝ (vector n) (sol.path s ω) ∂timeMeasure t)=
    inner ℝ (vector n) g+(∫ s,inner ℝ (vector n) (HeatControlAdapted.clamp U H (s,ω)) ∂timeMeasure t)+N t ω
  rw [hp] at hw
  linarith

end HeatModalWeakMaximum
#check @HeatModalWeakMaximum.exists_envelope
#print HeatModalWeakMaximum.exists_envelope
#print axioms HeatModalWeakMaximum.exists_envelope
