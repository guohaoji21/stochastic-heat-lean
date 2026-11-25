import HeatProgressiveControl
import HeatVolterraFixedPoint
import HeatVolterraForcing

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatControlledFixedPoint
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem exists_fixed_point (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (U : ℝ≥0 → Ω → E) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : E) :
    ∃ A u : Process (E := E) F μ H,
      u=HeatVolterraForcing.orbit F μ H S hS hcontr g+A+
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      (∀ v : Process (E := E) F μ H,
        v=HeatVolterraForcing.orbit F μ H S hS hcontr g+A+
          HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I v → v=u) ∧
      ∃ X : ℝ≥0 → Ω → E,
        (∀ ω, Continuous (fun t => X t ω)) ∧ StronglyAdapted F X ∧
        StronglyMeasurable[F.predictable] (Function.uncurry X) ∧
        (A=ᵐ[energyMeasure μ H] Function.uncurry X) ∧
        (∀ t, X t=ᵐ[μ] HeatControlConvolution.value H S (HeatControlAdapted.clamp U H) t) ∧
        ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0≤D ω) ∧ (∀ t ω, ‖X t ω‖≤D ω) ∧
          Integrable (fun ω => HeatPathMaximum.value H X ω^2) μ := by
  obtain ⟨A,X,hc,ha,hp,hAE,hrep,D,hDm,hD0,hB,hMax⟩ :=
    HeatProgressiveControl.exists_version F μ H S hS hcontr hn U hU hE
  obtain ⟨u,hu,hunique⟩ := HeatVolterraFixedPoint.exists_unique F μ H S hS hcontr M hsem I
    (HeatVolterraForcing.orbit F μ H S hS hcontr g+A)
  exact ⟨A,u,hu,hunique,X,hc,ha,hp,hAE,hrep,D,hDm,hD0,hB,hMax⟩

end HeatControlledFixedPoint
#check @HeatControlledFixedPoint.exists_fixed_point
#print HeatControlledFixedPoint.exists_fixed_point
#print axioms HeatControlledFixedPoint.exists_fixed_point
