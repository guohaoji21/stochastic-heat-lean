import HeatTorusMildTerminalControl
import HeatTorusGalerkinNullControl
import HeatTorusLiftedProjection

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5200000
set_option maxRecDepth 1600
noncomputable section

namespace HeatTorusTerminalComparison

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns UnitAddTorus
open HeatTorusGalerkinBackward (State laplace multiplier)
open HeatTorusGalerkinProjection (analysis)
open HeatTorusControlObservation (Control inject)
open HeatTorusLiftedProjection (analyze)
open HeatTorusProjectedConvolution (fullHeat)
open HeatTorusGalerkinTerminalDuality (diffusionResidual noiseBound)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

local notation "Ω" => C(ℝ≥0, ℝ)
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

local notation "J" => fun H S => HeatTerminalNaturality.integral F μ H
  (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar H)

local notation "V" => HeatTorusMildTerminalControl.state

/-- The projection of the actual locally controlled solution has the
same injected control as the finite equation and an explicit diffusion defect. -/
theorem project_state (P : ℝ) (b : C(UnitAddTorus ι, ℂ)) (O : Set (UnitAddTorus ι)) (H : ℝ≥0)
    (g : Full) (u : Process (E := Control O) F μ H) (S : Finset (ι → ℤ)) :
    ∃ X : HeatItoProductEnergy.Trajectory (J H S),
      (∀ t, X.state t = analyze μ S (V P b O H g u t)) ∧
      X.state 0 = Lp.const 2 μ (analysis S g) ∧
      (∀ᵐ t ∂timeMeasure H, X.drift t = ((laplace S P).compLpL 2 μ) (X.state t) +
        HeatBackwardEquationEnergy.slice (HeatPredictableObservation.lift F μ H (inject S O) u) t) ∧
      (∀ᵐ t ∂timeMeasure H, X.noise t = ((multiplier S b).compLpL 2 μ) (X.state t) +
        ((diffusionResidual S b).compLpL 2 μ) (V P b O H g u t)) := by
  let A := (analysis S).restrictScalars ℝ
  let f := HeatTorusMildTerminalControl.input O H u
  let uf := HeatPredictableObservation.lift F μ H (inject S O) u
  have hfm := HeatPredictableObservation.measurable_process F μ H f
  have hfq := HeatPredictableObservation.ambient_memLp F μ H f
  have hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)) :=
    (show IsStronglyPredictable F (Function.curry (f : ℝ≥0 × Ω → Full)) from Lp.stronglyMeasurable f).stronglyAdapted
  obtain ⟨hc, h₀, ha, huv, hVr⟩ := HeatTorusMildTerminalControl.state_properties P b O H g u
  obtain ⟨X, hx, hd, hn⟩ := HeatTorusProjectedForward.exists_trajectory F μ H S P b
    (HeatTorusMildTerminalControl.basis ι) (HeatTorusGalerkinBackward.basis S)
    (HeatCanonicalNative.scalar H) f hfm hfq hfa g (HeatTorusMildTerminalControl.process P b O H g u)
    (V P b O H g u) hc h₀ ha huv hVr
  refine ⟨X, hx, ?_, ?_, hn⟩
  · rw [show X.state 0 = analyze μ S (V P b O H g u 0) from hx 0, h₀,
      HeatTorusLiftedProjection.analyze_const]
  · have hfu : A ∘ f =ᵐ[energyMeasure μ H] (uf : ℝ≥0 × Ω → State S) := by
      filter_upwards [HeatPredictableObservation.lift_ae F μ H (HeatTorusMildTerminalControl.injection O) u,
        HeatPredictableObservation.lift_ae F μ H (inject S O) u] with p h₁ h₂
      change A (f p) = uf p
      change f p = _ at h₁
      change uf p = _ at h₂
      rw [h₁, h₂]
      rfl
    have hm := A.continuous.measurable.comp hfm
    have hq := A.lipschitzWith.comp_memLp (map_zero A) hfq
    filter_upwards [HeatTimeLpField.value_ae μ (A ∘ f) hm H hq,
      Measure.ae_ae_of_ae_prod hfu, HeatPredictableObservation.slice_ae F μ H uf] with t ht hu hs
    rw [hd t]
    congr 1
    apply Lp.ext
    have he : (fun ω => A (f (t, ω))) =ᵐ[μ] (fun ω => uf (t, ω)) := hu
    exact ht.trans (he.trans hs)

/-- When the same control nulls the finite equation, a projected terminal
pairing of the full equation is bounded by the diffusion defect alone. -/
theorem projected_pairing_sq_le (P : ℝ) (b : C(UnitAddTorus ι, ℂ)) (O : Set (UnitAddTorus ι))
    (H : ℝ≥0) (g : Full) (u : Process (E := Control O) F μ H)
    {C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (hb : ∀ x, (b x).im = 0)
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * HeatGevreyFourierExtension.weight k))
    (n : ℕ) (Z : HeatItoProductEnergy.Trajectory (J H (HeatTorusFrequencyExhaustion.box ι n)))
    (h₀ : Z.state 0 = Lp.const 2 μ (analysis (HeatTorusFrequencyExhaustion.box ι n) g))
    (hD : ∀ᵐ t ∂timeMeasure H, Z.drift t =
      ((laplace (HeatTorusFrequencyExhaustion.box ι n) P).compLpL 2 μ) (Z.state t) +
        HeatBackwardEquationEnergy.slice (HeatPredictableObservation.lift F μ H
          (inject (HeatTorusFrequencyExhaustion.box ι n) O) u) t)
    (hN : ∀ᵐ t ∂timeMeasure H, Z.noise t =
      ((multiplier (HeatTorusFrequencyExhaustion.box ι n) b).compLpL 2 μ) (Z.state t))
    (hEnd : Z.state H = 0)
    (η : Lp (State (HeatTorusFrequencyExhaustion.box ι n)) 2 μ)
    (hη : AEStronglyMeasurable[F H] (η : Ω → State (HeatTorusFrequencyExhaustion.box ι n)) μ) :
    (inner ℝ (analyze μ (HeatTorusFrequencyExhaustion.box ι n) (V P b O H g u H)) η) ^ 2 ≤
      (‖b‖ ^ 2 * (3 * HeatRegularKernel.mass (HeatTorusUniformTail.rate P n) *
        HeatForwardTailEnergy.energyBound H (HeatTorusGalerkinCompression.fullMultiplier b) g (‖u‖ ^ 2))) *
      (noiseBound b C decay H * ‖η‖ ^ 2) := by
  let S := HeatTorusFrequencyExhaustion.box ι n
  let w := HeatPredictableObservation.lift F μ H (inject S O) u
  let f := HeatBackwardEquationEnergy.slice w
  let path := V P b O H g u
  let err (t : ℝ≥0) := ((diffusionResidual S b).compLpL 2 μ) (path t)
  obtain ⟨X, hx, hx₀, hxD, hxN⟩ := project_state P b O H g u S
  obtain ⟨Y⟩ := HeatTorusGalerkinBackward.exists_solution S P b H η hη
  have hJ : StandardTerminalPastLocality (J H S) :=
    HeatTerminalNaturality.locality F μ H (HeatTorusGalerkinBackward.basis S)
      (HeatCanonicalNative.scalar H) (HeatCanonicalNative.locality H)
  have hf : MemLp f 2 (timeMeasure H) :=
    HeatTimeLpField.square_integrable μ w (HeatPredictableObservation.measurable_process F μ H w) H
      (HeatPredictableObservation.ambient_memLp F μ H w)
  have hc := (HeatTorusMildTerminalControl.state_properties P b O H g u).1
  obtain ⟨D, _, hDmax⟩ := HeatCompactLpBound.exists_bound μ H path hc
  have hV : MemLp path 2 (timeMeasure H) := by
    apply (memLp_const D).mono' hc.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem H] with t ht
    exact hDmax t ht.2
  let R := (diffusionResidual S b).compLpL 2 μ
  have he : MemLp err 2 (timeMeasure H) := R.lipschitzWith.comp_memLp (map_zero R) hV
  have hfwd := HeatTorusGalerkinTerminalDuality.terminal_pairing hJ hb Y X f err hf he hxD hxN
  have hfin := HeatTorusGalerkinTerminalDuality.terminal_pairing hJ hb Y Z f 0 hf
    (memLp_const (0 : Lp (State S) 2 μ)) hD (by simpa only [Pi.zero_apply, add_zero] using hN)
  simp only [hEnd, h₀, Pi.zero_apply, inner_zero_left, integral_zero, add_zero] at hfin
  rw [hx H, hx₀, ← hfin, zero_add] at hfwd
  rw [hfwd]
  have htail := HeatTorusMildTerminalControl.tail_le P b O H hP g u n
  unfold HeatForwardTailEnergy.trajectoryEnergy at htail
  simp_rw [HeatTorusLiftedProjection.lifted_tail_eq] at htail
  refine (HeatTorusGalerkinTerminalDuality.projected_defect_pairing_sq_le hP hC ha b hdec Y path hV).trans ?_
  have hn : 0 ≤ noiseBound b C decay H * ‖η‖ ^ 2 := by unfold noiseBound; positivity
  let P₀ := ((HeatTorusGalerkinProjection.project S).restrictScalars ℝ).compLpL 2 μ
  have hP₀ (x : Lp Full 2 μ) :
      P₀ x = ((HeatTorusGalerkinProjection.project S).compLpL 2 μ) x := by
    apply Lp.ext
    filter_upwards [((HeatTorusGalerkinProjection.project S).restrictScalars ℝ).coeFn_compLpL x,
      (HeatTorusGalerkinProjection.project S).coeFn_compLpL x] with ω h₁ h₂
    exact h₁.trans h₂.symm
  change (‖b‖ ^ 2 * (∫ s, ‖path s - P₀ (path s)‖ ^ 2 ∂timeMeasure H)) *
    (noiseBound b C decay H * ‖η‖ ^ 2) ≤ _
  simp_rw [hP₀]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail (sq_nonneg _)) hn

end HeatTorusTerminalComparison

#print axioms HeatTorusTerminalComparison.project_state
#print axioms HeatTorusTerminalComparison.projected_pairing_sq_le
