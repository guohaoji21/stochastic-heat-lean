import HeatTorusMildProjection
import HeatTorusHeatSmoothing
import HeatGeneralContinuous
import HeatForcingIdentification
import HeatCanonicalBDG

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusMildPath

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusGalerkinProjection (analysis)
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

/-- The canonical mild solution admits a predictable, adapted continuous
path version, with equality at every deterministic time including the terminal time. -/
theorem exists_version {P : ℝ} {T : ℝ≥0} (hT : 0 < T)
    {M : RealState ι →L[ℝ] RealState ι} [Nontrivial (RealState ι)]
    (U : ℝ≥0 → Ω → RealState ι) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ T))
    {g : RealState ι}
    (y : HeatTorusGevreyObstruction.MildSolution P T M (HeatControlAdapted.clamp U T) g) :
    ∃ Y : ℝ≥0 → Ω → RealState ι, (∀ ω, Continuous (fun t => Y t ω)) ∧
      StronglyAdapted F Y ∧ StronglyMeasurable[(F).predictable] (Function.uncurry Y) ∧
      y.process =ᵐ[energyMeasure μ T] Function.uncurry Y ∧
      ∀ t, t ≤ T → Y t =ᵐ[μ] y.value t := by
  let b := HeatTorusCanonicalIto.basis ι
  let J := HeatCanonicalNative.scalar T
  let I := HeatTerminalNaturality.integral F μ T b J
  let f := HeatControlAdapted.clamp U T
  let hn := HeatCanonicalNullComplete.contains_nulls
  have hsem (s t : ℝ≥0) : family (ι := ι) P (s + t) = (family P s).comp (family P t) :=
    realHeat_add P s.property t.property
  obtain ⟨_, X, hXc, hXa, _, _, hXr, D, hDm, hD0, hDb, _⟩ :=
    HeatProgressiveControl.exists_version F μ T (family P) (family_continuous P) (family_contraction P) hn U hU hE
  let A := y.process - HeatVolterraFixedPoint.convolution F μ T (family P)
    (family_continuous P) (family_contraction P) M hsem I y.process
  have hu : y.process = A + HeatVolterraFixedPoint.convolution F μ T (family P)
      (family_continuous P) (family_contraction P) M hsem I y.process := (sub_add_cancel _ _).symm
  let G (t : ℝ≥0) (ω : Ω) := family P t g + X t ω
  have hGc ω : Continuous (fun t => G t ω) := (family_continuous P g).add (hXc ω)
  have hGa : StronglyAdapted F G := fun t => stronglyMeasurable_const.add (hXa t)
  have hGp := SHE.ContinuousPredictable.stronglyMeasurable F G hGa hGc
  have hrep (t : ℝ≥0) : y.value t =ᵐ[μ] fun ω => G t ω +
      I.integral (HeatVolterraSlice.slice F μ T (family P) (family_continuous P) (family_contraction P) M t y.process) ω := by
    filter_upwards [y.equation t, hXr t] with ω hy hx
    change y.value t ω = family P t g + X t ω + _
    rw [hx]
    exact hy
  have hAG := HeatForcingIdentification.forcing_ae F μ T (family P) (family_continuous P)
    (family_contraction P) M hsem I A y.process hu y.value y.slices G
    (hGp.mono (predictable_le_product F)).measurable hrep
  have hsmooth (τ δ : ℝ≥0) (hτ : 0 < τ) (v : RealState ι) :
      ‖family P δ (family P τ v) - family P τ v‖ ≤ ((δ : ℝ) / (τ : ℝ)) ^ (3 / 8 : ℝ) * ‖v‖ :=
    HeatTorusHeatSmoothing.real_bound P (by exact_mod_cast hτ) δ.property (by norm_num) (by norm_num) v
  have hBDG : StandardTerminalBDGPower 8 I (SHEStochastic.NativeScalarBDG.constant 3) := by
    convert HeatCanonicalBDG.hilbert_bdg b T 3 using 1
  obtain ⟨Y, hYc, hYa, hYp, hYu, hYr⟩ :=
    HeatGeneralContinuous.exists_version F μ T (family P) (family_continuous P)
      (family_contraction P) M hsem hsmooth b J hT (HeatCanonicalNative.locality T)
      (HeatCanonicalNative.continuous_stopped T) hn _ hBDG A y.process hu G hGc hGa hAG
      (fun ω => ‖g‖ + D ω) ((memLp_const ‖g‖).add hDm)
      (fun ω => add_nonneg (norm_nonneg _) (hD0 ω))
      (fun t ω => (norm_add_le _ _).trans (add_le_add (family_contraction P t g) (hDb t ω)))
  exact ⟨Y, hYc, hYa, hYp, hYu, fun t ht => (hYr t ht).trans (hrep t).symm⟩

end HeatTorusMildPath

#print axioms HeatTorusMildPath.exists_version
