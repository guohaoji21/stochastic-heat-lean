import HeatTorusMildProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusFourierWeak

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusMildProjection (project)
open SHE.StoppedItoInputs
open scoped NNReal ENNReal

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

variable {P : ℝ} {T : ℝ≥0} {M : RealState ι →L[ℝ] RealState ι}
  {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}

local notation "Ito" S => HeatTerminalNaturality.integral F μ T
  (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar T)

/-- The integrated heat equation tested against all finite Fourier spaces.
The noise is formed from the full process before applying the projection. -/
def Holds (u : Process (E := RealState ι) F μ T)
    (V : ℝ≥0 → Lp (RealState ι) 2 μ) : Prop :=
  ∀ (S : Finset (ι → ℤ)) (t : ℝ≥0), t ≤ T →
    ((project S).compLpL 2 μ) (V t) =
      ((project S).compLpL 2 μ) (Lp.const 2 μ g) +
      (∫ r, ((HeatTorusGalerkinBackward.laplace S P).compLpL 2 μ)
        (((project S).compLpL 2 μ) (V r)) + HeatTimeLpField.value μ (project S ∘ f) r ∂timeMeasure t) +
      HeatStoppedPairing.value F μ T (Ito S) (HeatPredictableObservation.lift F μ T ((project S).comp M) u) t

/-- A mild solution satisfies the integrated equation in each test space,
using the unchanged full diffusion, state and deterministic time values. -/
theorem of_mild (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g) :
    Holds (P := P) (M := M) (f := f) (g := g) y.process y.value := by
  intro S t ht
  obtain ⟨X, hX, hd, hn⟩ := HeatTorusMildProjection.projected_trajectory S hf hfi hfa y
  let A := (project S).comp M
  let u := HeatPredictableObservation.lift F μ T A y.process
  have hu : X.process = u := by
    apply HeatPredictableObservation.eq_of_slices F μ T
    filter_upwards [X.noise_slices, hn, HeatPredictableObservation.lift_slices F μ T A y.process y.value y.slices]
      with r h₁ h₂ h₃
    rw [h₂] at h₁
    exact h₁.trans h₃.symm
  have h := X.equation t ht
  unfold HeatDeterministicPairing.cumulative at h
  rw [HeatTimeRestriction.restrict_Iio ht] at h
  simp_rw [hd, hX, y.initial_value, hu] at h
  exact h

/-- A continuous adapted family satisfying the Fourier weak identity gives
an Itô trajectory on each finite set of modes. -/
theorem trajectory (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (u : Process (E := RealState ι) F μ T) (V : ℝ≥0 → Lp (RealState ι) 2 μ)
    (hc : Continuous V) (h0 : V 0 = Lp.const 2 μ g)
    (ha : ∀ r, AEStronglyMeasurable[F r] (V r : Ω → RealState ι) μ)
    (hu : ∀ᵐ r ∂timeMeasure T, (fun ω => u (r, ω)) =ᵐ[μ] V r)
    (hw : Holds (P := P) (M := M) (f := f) (g := g) u V) (S : Finset (ι → ℤ)) :
    ∃ X : HeatItoProductEnergy.Trajectory (Ito S),
      (∀ t, X.state t = ((project S).compLpL 2 μ) (V t)) ∧
      (∀ t, X.drift t = ((HeatTorusGalerkinBackward.laplace S P).compLpL 2 μ) (X.state t) +
        HeatTimeLpField.value μ (project S ∘ f) t) ∧
      (∀ t, X.noise t = (((project S).comp M).compLpL 2 μ) (V t)) := by
  let A := project S
  let D := A.comp M
  let L := HeatTorusGalerkinBackward.laplace S P
  let x (r : ℝ≥0) := (A.compLpL 2 μ) (V r)
  let q := HeatTimeLpField.value μ (A ∘ f)
  let v := HeatPredictableObservation.lift F μ T D u
  have hx : Continuous x := (A.compLpL 2 μ).continuous.comp hc
  have hxa (r : ℝ≥0) : AEStronglyMeasurable[F r] (x r : Ω → Finite S) μ :=
    (A.continuous.comp_aestronglyMeasurable (ha r)).congr (A.coeFn_compLpL (V r)).symm
  have hxm : MemLp x 2 (timeMeasure T) := by
    obtain ⟨K, hK, h⟩ := HeatCompactLpBound.exists_bound μ T x hx
    apply (memLp_const K).mono' hx.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem T] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg hK] using h _ ht.2
  have hV : MemLp V 2 (timeMeasure T) := by
    obtain ⟨K, hK, h⟩ := HeatCompactLpBound.exists_bound μ T V hc
    apply (memLp_const K).mono' hc.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem T] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg hK] using h _ ht.2
  have hq := HeatTimeLpField.square_integrable μ (A ∘ f) (A.continuous.measurable.comp hf) T
    (A.lipschitzWith.comp_memLp (map_zero A) hfi)
  refine ⟨{
    state := x
    drift := fun r => (L.compLpL 2 μ) (x r) + q r
    noise := fun r => (D.compLpL 2 μ) (V r)
    process := v
    state_square := hxm
    drift_square := ?_
    noise_square := (D.compLpL 2 μ).lipschitzWith.comp_memLp (map_zero _) hV
    initial_adapted := hxa 0
    drift_adapted := ?_
    noise_slices := HeatPredictableObservation.lift_slices F μ T D u V hu
    equation := ?_ }, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · exact ((L.compLpL 2 μ).lipschitzWith.comp_memLp (map_zero _) hxm).add hq
  · apply Eventually.of_forall
    intro t
    have hqa := HeatTimeLpDrift.adapted μ (A ∘ f) F (fun r => A.continuous.comp_stronglyMeasurable (hfa r)) t
    exact (((L.continuous.comp_aestronglyMeasurable (hxa t)).congr
      (L.coeFn_compLpL (x t)).symm).add hqa).congr (Lp.coeFn_add _ _).symm
  · intro t ht
    unfold HeatDeterministicPairing.cumulative
    rw [HeatTimeRestriction.restrict_Iio ht]
    dsimp only [x]
    rw [h0]
    exact hw S t ht
end HeatTorusFourierWeak

#print axioms HeatTorusFourierWeak.of_mild
#print axioms HeatTorusFourierWeak.trajectory
