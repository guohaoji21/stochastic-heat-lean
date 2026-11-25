import HeatTorusGevreyObstruction
import HeatTorusProjectedForward
import HeatTorusMildTerminalControl
import HeatMildSpatialTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusMildProjection

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

/-- Real states projected onto finitely many complex Fourier modes. -/
def project (S : Finset (ι → ℤ)) : RealState ι →L[ℝ] Finite S :=
  ((analysis S).restrictScalars ℝ).comp embed

/-- Every mild solution in the paper induces finite projected Itô trajectories
driven by the same canonical Brownian motion. The diffusion is the projection
of the original full diffusion. -/
theorem projected_trajectory (S : Finset (ι → ℤ)) {P : ℝ} {T : ℝ≥0}
    {M : RealState ι →L[ℝ] RealState ι} {f : ℝ≥0 × Ω → RealState ι} (hf : Measurable f)
    (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω))) {g : RealState ι}
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g) :
    let J := HeatCanonicalNative.scalar T
    let L := HeatTorusGalerkinBackward.laplace S P
    ∃ X : HeatItoProductEnergy.Trajectory (HeatTerminalNaturality.integral F μ T
        (HeatTorusGalerkinBackward.basis S) J),
      (∀ t, X.state t = ((project S).compLpL 2 μ) (y.value t)) ∧
      (∀ t, X.drift t = (L.compLpL 2 μ) (X.state t) + HeatTimeLpField.value μ (project S ∘ f) t) ∧
      (∀ᵐ t ∂timeMeasure T, X.noise t = (((project S).comp M).compLpL 2 μ) (y.value t)) := by
  dsimp only
  let e : RealState ι →L[ℝ] Full := embed
  let N := e.comp (M.comp realPart)
  let v := HeatPredictableObservation.lift F μ T e y.process
  let V (t : ℝ≥0) := (e.compLpL 2 μ) (y.value t)
  let β := HeatTorusMildTerminalControl.basis ι
  let J := HeatCanonicalNative.scalar T
  let I := HeatTorusCanonicalIto.integral ι T
  let I' := HeatTerminalNaturality.integral F μ T β J
  have hN (w : RealState ι) : e (M w) = N (e w) := by
    change e (M w) = e (M (realPart (embed w)))
    rw [realPart_embed]
  have hS (t : ℝ≥0) (w : RealState ι) : e (family P t w) = fullHeat P t (e w) :=
    embed_realHeat P t w
  have hv0 : V 0 = Lp.const 2 μ (e g) := by
    change (e.compLpL 2 μ) (y.value 0) = _
    rw [y.initial_value]
    apply Lp.ext
    filter_upwards [e.coeFn_compLpL (Lp.const 2 μ g), Lp.coeFn_const 2 μ g,
      Lp.coeFn_const 2 μ (e g)] with ω h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    rfl
  have hva (t : ℝ≥0) : ∃ Z : Ω → Full, StronglyMeasurable[F t] Z ∧ V t =ᵐ[μ] Z := by
    obtain ⟨Z, hZ, hz⟩ := y.adapted_value t
    exact ⟨e ∘ Z, e.continuous.comp_stronglyMeasurable hZ,
      (e.coeFn_compLpL (y.value t)).trans (hz.fun_comp e)⟩
  have hvs : ∀ᵐ t ∂timeMeasure T, (fun ω => v (t, ω)) =ᵐ[μ] V t := by
    filter_upwards [Measure.ae_ae_of_ae_prod (HeatPredictableObservation.lift_ae F μ T e y.process),
      y.slices] with t hv hy
    have hv' : (fun ω => v (t, ω)) =ᵐ[μ] fun ω => e (y.process (t, ω)) := hv
    have hy' : (fun ω => y.process (t, ω)) =ᵐ[μ] y.value t := hy
    exact hv'.trans ((hy'.fun_comp e).trans (e.coeFn_compLpL (y.value t)).symm)
  have hvr (t : ℝ≥0) : V t =ᵐ[μ] fun ω => fullHeat P t (e g) +
      HeatControlConvolution.value T (fullHeat P) (e ∘ f) t ω +
      I'.integral (HeatVolterraSlice.slice F μ T (fullHeat P) (fullHeat_continuous P)
        (fullHeat_contraction P) N t v) ω := by
    let d := HeatVolterraSlice.slice F μ T (family P) (family_continuous P) (family_contraction P) M t y.process
    let d' := HeatVolterraSlice.slice F μ T (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P) N t v
    have he : (e.compLpL 2 μ) (I.integral d) = I'.integral d' := by
      change (e.compLpL 2 μ) ((HeatTerminalNaturality.integral F μ T (HeatTorusCanonicalIto.basis ι) J).integral d) = _
      rw [HeatTerminalCrossNaturality.commutes F μ T (HeatTorusCanonicalIto.basis ι) β J e]
      change I'.integral (HeatPredictableObservation.lift F μ T e d) = I'.integral d'
      congr 1
      exact HeatMildSpatialTransport.slice F μ T (family P) (family_continuous P)
        (family_contraction P) (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P) e hS M N hN t y.process
    have hc := HeatMildSpatialTransport.control_value μ T (family P) (family_continuous P)
      (family_contraction P) (fullHeat P) e hS f hf hfi (e ∘ f) EventuallyEq.rfl t
    filter_upwards [e.coeFn_compLpL (y.value t), y.equation t, hc, e.coeFn_compLpL (I.integral d)]
      with ω hv hy hcontrol hnoise
    change V t ω = e (y.value t ω) at hv
    change y.value t ω = family P t g + HeatControlConvolution.value T (family P) f t ω + I.integral d ω at hy
    change V t ω = fullHeat P t (e g) + HeatControlConvolution.value T (fullHeat P) (e ∘ f) t ω + I'.integral d' ω
    rw [hv, hy, map_add, map_add, hS, hcontrol, ← hnoise, he]
  obtain ⟨X, hx, hd, hn⟩ := HeatTorusProjectedForward.exists_projected_trajectory F μ T S P N β
    (HeatTorusGalerkinBackward.basis S) J (e ∘ f) (e.continuous.measurable.comp hf)
    (e.lipschitzWith.comp_memLp (map_zero e) hfi) (fun t => e.continuous.comp_stronglyMeasurable (hfa t))
    (e g) v V ((e.compLpL 2 μ).continuous.comp y.continuous_value) hv0 hva hvs hvr
  refine ⟨X, fun t => ?_, hd, ?_⟩
  · rw [hx t]
    exact HeatTerminalNaturality.compLp_comp μ ((analysis S).restrictScalars ℝ) e (y.value t)
  · filter_upwards [hn] with t ht
    rw [ht]
    let A := (analysis S).restrictScalars ℝ
    have hcomp : (A.comp N).comp e = (project S).comp M := by
      apply ContinuousLinearMap.ext
      intro w
      exact congrArg A (hN w).symm
    change (((A.comp N).compLpL 2 μ) ((e.compLpL 2 μ) (y.value t))) = _
    simp only [HeatTerminalNaturality.compLp_comp, hcomp]

end HeatTorusMildProjection

#print axioms HeatTorusMildProjection.projected_trajectory
