import HeatTorusFourierWeak
import HeatTorusSpectralForm
import HeatCompactTimeIntegrability

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

def stateResidual (u : Process (E := RealState ι) F μ T)
    (V : ℝ≥0 → Lp (RealState ι) 2 μ) (t : ℝ≥0) : Lp (RealState ι) 2 μ :=
  V t - (Lp.const 2 μ g +
    (∫ r, HeatTimeLpField.value μ f r ∂timeMeasure t) +
    HeatStoppedPairing.value F μ T (HeatTorusCanonicalIto.integral ι T)
      (HeatPredictableObservation.lift F μ T M u) t)

def fullPair (φ : Full) (X : Lp Full 2 μ) : Lp ℝ 2 μ :=
  ((innerSL ℝ φ).compLpL 2 μ) X

/-- The weak spatial equation in the physical Sobolev form.
Pairings are real, as the real space is embedded in its complexification. -/
def Holds (u : Process (E := RealState ι) F μ T) (V : ℝ≥0 → Lp (RealState ι) 2 μ)
    (D : ι → (ℝ≥0 × Ω) → Full) : Prop :=
  ∀ (t : ℝ≥0), t ≤ T → ∀ (φ : Full) (E : ι → Full), HeatTorusGradient.HasGradient P φ E →
    fullPair φ ((embed.compLpL 2 μ) (stateResidual (M := M) (f := f) (g := g) u V t)) =
      -∑ i, fullPair (E i) (∫ r, HeatTimeLpField.value μ (D i) r ∂timeMeasure t)

theorem of_polynomial_tests (P : ℝ) (x : Lp Full 2 μ) (Q : ι → Lp Full 2 μ)
    (h : ∀ (S : Finset (ι → ℤ)) (φ : Full) (E : ι → Full),
      HeatTorusGradient.HasGradient P φ E →
      fullPair (HeatTorusGalerkinProjection.project S φ) x =
        -∑ i, fullPair (HeatTorusGalerkinProjection.project S (E i)) (Q i))
    (φ : Full) (E : ι → Full) (hE : HeatTorusGradient.HasGradient P φ E) :
    fullPair φ x = -∑ i, fullPair (E i) (Q i) := by
  let L (φ : Full) := fullPair φ x
  let R (E : ι → Full) := -∑ i, fullPair (E i) (Q i)
  have hL : Continuous L := (((innerSL ℝ).compLpL₂ 2 μ).flip x).continuous
  have hR : Continuous R := by
    unfold R
    apply Continuous.neg
    apply continuous_finsetSum
    intro i _
    exact ((((innerSL ℝ).compLpL₂ 2 μ).flip (Q i)).continuous).comp (continuous_apply i)
  have hφ := HeatTorusGalerkinProjection.project_tendsto φ
  have hE' : Tendsto (fun S : Finset (ι → ℤ) => fun i => HeatTorusGalerkinProjection.project S (E i))
      atTop (𝓝 E) :=
    tendsto_pi_nhds.mpr fun i => HeatTorusGalerkinProjection.project_tendsto (E i)
  have hleft : Tendsto (fun S => L (HeatTorusGalerkinProjection.project S φ)) atTop (𝓝 (L φ)) :=
    hL.continuousAt.tendsto.comp hφ
  have hright : Tendsto (fun S => R (fun i => HeatTorusGalerkinProjection.project S (E i)))
      atTop (𝓝 (R E)) := hR.continuousAt.tendsto.comp hE'
  have hsame : (fun S : Finset (ι → ℤ) => L (HeatTorusGalerkinProjection.project S φ)) =
      (fun S : Finset (ι → ℤ) => R (fun i => HeatTorusGalerkinProjection.project S (E i))) :=
    funext fun S => h S φ E hE
  rw [hsame] at hleft
  exact tendsto_nhds_unique hleft hright

private theorem project_force {S : Finset (ι → ℤ)} (A : RealState ι →L[ℝ] Finite S)
    (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (t : ℝ≥0) (ht : t ≤ T) :
    (A.compLpL 2 μ) (∫ r, HeatTimeLpField.value μ f r ∂timeMeasure t) =
      ∫ r, HeatTimeLpField.value μ (A ∘ f) r ∂timeMeasure t := by
  have hft := hfi.mono_measure (Measure.prod_mono (HeatTimeRestriction.mono ht) le_rfl)
  have hAf := A.lipschitzWith.comp_memLp (map_zero A) hft
  have hA := A.continuous.measurable.comp hf
  rw [← (A.compLpL 2 μ).integral_comp_comm
    ((HeatTimeLpField.square_integrable μ f hf t hft).integrable one_le_two)]
  apply integral_congr_ae
  filter_upwards [HeatTimeLpField.value_ae μ f hf t hft,
    HeatTimeLpField.value_ae μ (A ∘ f) hA t hAf] with r h₁ h₂
  apply Lp.ext
  filter_upwards [h₁, h₂, A.coeFn_compLpL (HeatTimeLpField.value μ f r)] with ω h₁ h₂ h₃
  rw [h₃, h₁, h₂] <;> rfl

theorem projected_residual (u : Process (E := RealState ι) F μ T)
    (V : ℝ≥0 → Lp (RealState ι) 2 μ) (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (S : Finset (ι → ℤ)) (t : ℝ≥0) (ht : t ≤ T) :
    ((project S).compLpL 2 μ) (stateResidual (M := M) (f := f) (g := g) u V t) =
      ((project S).compLpL 2 μ) (V t) -
        (((project S).compLpL 2 μ) (Lp.const 2 μ g) +
        (∫ r, HeatTimeLpField.value μ (project S ∘ f) r ∂timeMeasure t) +
        HeatStoppedPairing.value F μ T (HeatTerminalNaturality.integral F μ T
          (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar T))
          (HeatPredictableObservation.lift F μ T ((project S).comp M) u) t) := by
  unfold stateResidual
  rw [map_sub, map_add, map_add, project_force (project S) hf hfi t ht]
  have h := HeatTerminalCrossNaturality.stopped_commutes F μ T
    (HeatTorusCanonicalIto.basis ι) (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar T)
    (project S) t (HeatPredictableObservation.lift F μ T M u)
  have hlift : HeatPredictableObservation.lift F μ T (project S) (HeatPredictableObservation.lift F μ T M u) =
      HeatPredictableObservation.lift F μ T ((project S).comp M) u := by
    unfold HeatPredictableObservation.lift
    let : MeasurableSpace (ℝ≥0 × Ω) := (F).predictable
    exact HeatTerminalNaturality.compLp_comp _ (project S) M u
  change ((project S).compLpL 2 μ) (HeatStoppedPairing.value F μ T (HeatTorusCanonicalIto.integral ι T)
      (HeatPredictableObservation.lift F μ T M u) t) =
    HeatStoppedPairing.value F μ T (HeatTerminalNaturality.integral F μ T
      (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar T))
      (HeatPredictableObservation.lift F μ T (project S) (HeatPredictableObservation.lift F μ T M u)) t at h
  rw [h, hlift]

theorem scalar_project_pair (S : Finset (ι → ℤ)) (z : Finite S)
    (X : Lp (RealState ι) 2 μ) :
    fullPair (HeatTorusGalerkinProjection.synthesis S z) ((embed.compLpL 2 μ) X) =
      ((innerSL ℝ z).compLpL 2 μ) (((project S).compLpL 2 μ) X) := by
  let v := HeatTorusGalerkinProjection.synthesis S z
  let e : RealState ι →L[ℝ] Full := embed
  let A := project S
  have h : (innerSL ℝ v).comp e = (innerSL ℝ z).comp A := by
    apply ContinuousLinearMap.ext
    intro x
    change (inner ℂ (HeatTorusGalerkinProjection.synthesis S z) (embed x)).re =
      (inner ℂ z (HeatTorusGalerkinProjection.analysis S (embed x))).re
    exact congrArg Complex.re ((HeatTorusGalerkinProjection.synthesis S).adjoint_inner_right _ _).symm
  change ((innerSL ℝ v).compLpL 2 μ) ((e.compLpL 2 μ) X) =
    ((innerSL ℝ z).compLpL 2 μ) ((A.compLpL 2 μ) X)
  rw [HeatTerminalNaturality.compLp_comp μ (innerSL ℝ v) e X,
    HeatTerminalNaturality.compLp_comp μ (innerSL ℝ z) A X, h]


end HeatTorusVariationalForm

#print axioms HeatTorusVariationalForm.projected_residual
#print axioms HeatTorusVariationalForm.of_polynomial_tests
