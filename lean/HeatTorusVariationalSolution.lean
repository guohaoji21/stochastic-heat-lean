import HeatTorusVariationalForm
import HeatTorusFourierUniqueness
import HeatTorusMildGradient
import HeatTorusMildPath
import HeatTorusMildMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusVariationalSolution

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

/-- A continuous variational solution on the paper's fixed Wiener space.
The weak gradients are those of the continuous path for product-a.e. time.
The integrated identity uses the same deterministic forcing and Itô integral. -/
structure Solution (P : ℝ) (T : ℝ≥0) (M : RealState ι →L[ℝ] RealState ι)
    (f : ℝ≥0 × Ω → RealState ι) (g : RealState ι) where
  process : Process (E := RealState ι) F μ T
  path : ℝ≥0 → Ω → RealState ι
  path_continuous : ∀ ω, Continuous (fun t => path t ω)
  path_adapted : StronglyAdapted F path
  path_agrees : process =ᵐ[energyMeasure μ T] Function.uncurry path
  value : ℝ≥0 → Lp (RealState ι) 2 μ
  continuous_value : Continuous value
  initial_value : value 0 = Lp.const 2 μ g
  adapted_value : ∀ t, AEStronglyMeasurable[F t] (value t : Ω → RealState ι) μ
  path_value : ∀ t, t ≤ T → path t =ᵐ[μ] value t
  slices : ∀ᵐ t ∂SHE.PredictableL2.timeMeasure T, (fun ω => process (t, ω)) =ᵐ[μ] value t
  gradient : ι → (ℝ≥0 × Ω) → Full
  gradient_predictable : ∀ i, StronglyMeasurable[(F).predictable] (gradient i)
  gradient_integrable : ∀ i, MemLp (gradient i) 2 (energyMeasure μ T)
  weak_gradient : ∀ᵐ p ∂energyMeasure μ T,
    HeatTorusGradient.HasGradient P (embed (process p)) (fun i => gradient i p)
  equation : HeatTorusVariationalForm.Holds (P := P) (M := M) (f := f) (g := g) process value gradient
  maximum_energy : Integrable (fun ω => HeatPathMaximum.value T path ω ^ 2) μ

theorem Solution.gradient_measurable
    {P : ℝ} {T : ℝ≥0} {M : RealState ι →L[ℝ] RealState ι}
    {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}
    (z : Solution P T M f g) (i : ι) : Measurable (z.gradient i) :=
  (z.gradient_predictable i).measurable.mono (predictable_le_product F) le_rfl

theorem value_eq_mild {P : ℝ} {T : ℝ≥0}
    {M : RealState ι →L[ℝ] RealState ι} {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}
    (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g)
    (z : Solution P T M f g) (t : ℝ≥0) (ht : t ≤ T) :
    z.value t = y.value t := by
  exact HeatTorusFourierUniqueness.value_eq_mild hf hfi hfa y z.process z.value z.continuous_value
    z.initial_value z.adapted_value z.slices
    ((HeatTorusVariationalForm.iff_fourier z.process z.value z.continuous_value z.slices hf hfi
      z.gradient z.gradient_measurable z.gradient_integrable z.weak_gradient).mp z.equation) t ht

/-- The same equality holds in the predictable product space used by the
stochastic integrals. -/
theorem process_eq_mild {P : ℝ} {T : ℝ≥0}
    {M : RealState ι →L[ℝ] RealState ι} {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}
    (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g)
    (z : Solution P T M f g) : z.process = y.process := by
  apply HeatPredictableObservation.eq_of_slices F μ T
  filter_upwards [z.slices, y.slices, timeMeasure_ae_mem T] with t hz hy ht
  rw [value_eq_mild hf hfi hfa y z t ht.2] at hz
  exact hz.trans hy.symm
theorem terminal_eq_mild {P : ℝ} {T : ℝ≥0}
    {M : RealState ι →L[ℝ] RealState ι} {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}
    (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g)
    (z : Solution P T M f g) : z.path T =ᵐ[μ] y.value T := by
  rw [← value_eq_mild hf hfi hfa y z T le_rfl]
  exact z.path_value T le_rfl

theorem of_mild {P : ℝ} {T : ℝ≥0} (hT : 0 < T)
    {M : RealState ι →L[ℝ] RealState ι} [Nontrivial (RealState ι)]
    (U : ℝ≥0 → Ω → RealState ι) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ T))
    {g : RealState ι}
    (y : HeatTorusGevreyObstruction.MildSolution P T M (HeatControlAdapted.clamp U T) g) :
    ∃ z : Solution P T M (HeatControlAdapted.clamp U T) g, z.value = y.value := by
  let f := HeatControlAdapted.clamp U T
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F U hU T).measurable
  have hfi : MemLp f 2 (energyMeasure μ T) := HeatClampedControl.square_integrable F μ T U hU hE
  have hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)) :=
    (HeatControlAdapted.clamp_progressive F U hU T).stronglyAdapted
  obtain ⟨Y, hYc, hYa, _, hY, hYv⟩ := HeatTorusMildPath.exists_version hT U hU hE y
  obtain ⟨D, hDp, hDi, hD⟩ := HeatTorusMildGradient.exists_gradient hf hfi hfa y
  have hDm (i : ι) : Measurable (D i) := (hDp i).measurable.mono (predictable_le_product F) le_rfl
  have hW := HeatTorusFourierWeak.of_mild hf hfi hfa y
  have hV := (HeatTorusVariationalForm.iff_fourier y.process y.value y.continuous_value
    y.slices hf hfi D hDm hDi hD).mpr hW
  have hmax := HeatTorusMildMaximum.integrable_maximum hf hfi hfa y Y hYc hYa hYv hY
  exact ⟨⟨y.process, Y, hYc, hYa, hY, y.value, y.continuous_value, y.initial_value, y.adapted_value,
    hYv, y.slices, D, hDp, hDi, hD, hV, hmax⟩, rfl⟩

/-- For progressive finite-energy forcing on the canonical Wiener space,
the mild and continuous variational formulations have the same solution
at every time through the terminal time. -/
theorem exists_corresponding {P : ℝ} {T : ℝ≥0} (hT : 0 < T)
    (M : RealState ι →L[ℝ] RealState ι) [Nontrivial (RealState ι)]
    (U : ℝ≥0 → Ω → RealState ι) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ T))
    (g : RealState ι) :
    let f := HeatControlAdapted.clamp U T
    ∃ y : HeatTorusGevreyObstruction.MildSolution P T M f g,
      (∃ z : Solution P T M f g, z.value = y.value) ∧
      ∀ z : Solution P T M f g, z.path T =ᵐ[μ] y.value T := by
  dsimp only
  have hsem (s t : ℝ≥0) : family (ι := ι) P (s + t) = (family P s).comp (family P t) :=
    realHeat_add P s.property t.property
  obtain ⟨_, u, V, _, hc, h0, ha, hs, he⟩ :=
    HeatControlledMild.exists_solution F μ T (family P) (family_continuous P) (family_contraction P)
      M hsem (HeatTorusCanonicalIto.integral ι T) (realHeat_zero P)
      HeatCanonicalNullComplete.contains_nulls U hU hE g
  let y : HeatTorusGevreyObstruction.MildSolution P T M (HeatControlAdapted.clamp U T) g :=
    ⟨u, V, hc, h0, fun t => by
      obtain ⟨A, hA, hAv⟩ := ha t
      exact hA.aestronglyMeasurable.congr hAv.symm, hs, he⟩
  refine ⟨y, of_mild hT U hU hE y, fun z => ?_⟩
  exact terminal_eq_mild (HeatControlAdapted.clamp_measurable F U hU T).measurable
    (HeatClampedControl.square_integrable F μ T U hU hE)
    (HeatControlAdapted.clamp_progressive F U hU T).stronglyAdapted y z
end HeatTorusVariationalSolution

#print axioms HeatTorusVariationalSolution.of_mild
#print axioms HeatTorusVariationalSolution.terminal_eq_mild
#print axioms HeatTorusVariationalSolution.process_eq_mild
#print axioms HeatTorusVariationalSolution.exists_corresponding
