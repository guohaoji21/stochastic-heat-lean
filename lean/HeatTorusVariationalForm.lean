import HeatTorusVariationalPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace HeatTorusVariationalForm

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusMildProjection (project)
open SHE.StoppedItoInputs
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local notation "Finite" => HeatTorusGalerkinBackward.State
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (Finite S) :=
  InnerProductSpace.rclikeToReal ℂ (Finite S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (Finite S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (Finite S) := ⟨rfl⟩
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "Ω" => C(ℝ≥0, ℝ)
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable

local instance : InnerProductSpace ℝ Full := InnerProductSpace.rclikeToReal ℂ Full

variable {P : ℝ} {T : ℝ≥0} {M : RealState ι →L[ℝ] RealState ι}
  {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}

/-- The Fourier weak equation and the Sobolev variational equation are
equivalent when the trajectory has square-integrable weak gradients. -/
theorem iff_fourier (u : Process (E := RealState ι) F μ T) (V : ℝ≥0 → Lp (RealState ι) 2 μ)
    (hc : Continuous V)
    (hu : ∀ᵐ r ∂timeMeasure T, (fun ω => u (r, ω)) =ᵐ[μ] V r)
    (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (D : ι → (ℝ≥0 × Ω) → Full) (hDm : ∀ i, Measurable (D i))
    (hDi : ∀ i, MemLp (D i) 2 (energyMeasure μ T))
    (hD : ∀ᵐ p ∂energyMeasure μ T, HeatTorusGradient.HasGradient P (embed (u p)) (fun i => D i p)) :
    Holds (P := P) (M := M) (f := f) (g := g) u V D ↔
      HeatTorusFourierWeak.Holds (P := P) (M := M) (f := f) (g := g) u V := by
  have hsplit (t : ℝ≥0) (ht : t ≤ T) (S : Finset (ι → ℤ)) :
      (∫ r, ((HeatTorusGalerkinBackward.laplace S P).compLpL 2 μ) (((project S).compLpL 2 μ) (V r)) +
         HeatTimeLpField.value μ (project S ∘ f) r ∂timeMeasure t) =
        (∫ r, ((HeatTorusGalerkinBackward.laplace S P).compLpL 2 μ) (((project S).compLpL 2 μ) (V r))
          ∂timeMeasure t) + ∫ r, HeatTimeLpField.value μ (project S ∘ f) r ∂timeMeasure t := by
    let A := project S
    let L := HeatTorusGalerkinBackward.laplace S P
    let x (r : ℝ≥0) := (L.compLpL 2 μ) ((A.compLpL 2 μ) (V r))
    have hxc : Continuous x := (L.compLpL 2 μ).continuous.comp ((A.compLpL 2 μ).continuous.comp hc)
    have hxi : Integrable x (timeMeasure t) := by
      obtain ⟨K, _, h⟩ := HeatCompactLpBound.exists_bound μ t x hxc
      apply (integrable_const K).mono' hxc.aestronglyMeasurable
      filter_upwards [timeMeasure_ae_mem t] with q hq
      exact h q hq.2
    apply integral_add hxi
    exact (HeatTimeLpField.square_integrable μ (A ∘ f) (A.continuous.measurable.comp hf) t
      (A.lipschitzWith.comp_memLp (map_zero A)
        (hfi.mono_measure (Measure.prod_mono (HeatTimeRestriction.mono ht) le_rfl)))).integrable one_le_two
  have key (S : Finset (ι → ℤ)) (t : ℝ≥0) (ht : t ≤ T) :
      ((project S).compLpL 2 μ) (stateResidual (M := M) (f := f) (g := g) u V t) =
        (∫ r, ((HeatTorusGalerkinBackward.laplace S P).compLpL 2 μ) (((project S).compLpL 2 μ) (V r))
          ∂timeMeasure t) ↔
      ((project S).compLpL 2 μ) (V t) =
        ((project S).compLpL 2 μ) (Lp.const 2 μ g) +
        (∫ r, ((HeatTorusGalerkinBackward.laplace S P).compLpL 2 μ) (((project S).compLpL 2 μ) (V r)) +
          HeatTimeLpField.value μ (project S ∘ f) r ∂timeMeasure t) +
        HeatStoppedPairing.value F μ T (HeatTerminalNaturality.integral F μ T
          (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar T))
          (HeatPredictableObservation.lift F μ T ((project S).comp M) u) t := by
    rw [projected_residual u V hf hfi S t ht, hsplit t ht S, sub_eq_iff_eq_add]
    constructor <;> intro h <;> rw [h] <;> abel
  constructor
  · intro h S t ht
    apply (key S t ht).mp
    apply HeatLpSpatialExt.ext μ
    intro z
    obtain ⟨E, hE⟩ := HeatTorusGradient.exists_gradient_of_generator P _ _
      (HeatTorusSpectralForm.synthesis_generator P S z)
    rw [← scalar_project_pair]
    exact (h t ht _ E hE).trans
      (finite_gradient_form t ht S z E hE u V hc hu D hDm hDi hD).symm
  · intro h
    intro t ht φ E hE
    refine of_polynomial_tests P _ _ ?_ φ E hE
    intro S ψ G hG
    let z := HeatTorusGalerkinProjection.analysis S ψ
    have hp := HeatTorusSpectralForm.project_gradient P S ψ G hG
    change fullPair (HeatTorusGalerkinProjection.synthesis S z) _ = _
    rw [scalar_project_pair, (key S t ht).mpr (h S t ht)]
    exact finite_gradient_form t ht S z _ hp u V hc hu D hDm hDi hD
end HeatTorusVariationalForm

#print axioms HeatTorusVariationalForm.iff_fourier
