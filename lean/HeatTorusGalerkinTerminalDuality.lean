import HeatBackwardProductTrajectory
import HeatTorusAnalyticInterpolation
import HeatTorusGalerkinCompression
import HeatMildCellPairing
import HeatIntegralCauchy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace HeatTorusGalerkinTerminalDuality

open Filter MeasureTheory SHE SHE.PredictableL2 UnitAddTorus
open HeatTorusGalerkinBackward (State laplace multiplier)
open HeatGevreyFourierExtension (weight)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

section Pairing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [IsSeparable μ] {H : ℝ≥0}
  {S : Finset (ι → ℤ)} {J : StandardTerminalIto (C := State S) (E := State S) F μ H}

omit [Fintype ι] [IsSeparable μ] in
private theorem adjoint_lift_eq (A : State S →L[ℝ] State S)
    (hs : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) :
    (A.compLpL 2 μ).adjoint = A.compLpL 2 μ := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact HeatMildCellPairing.lifted_self_adjoint μ A hs y x

/-- A projected forward equation pairs with the true finite Galerkin
backward solution. The remaining diffusion term is exactly the error
introduced by the projection of the forward equation. -/
theorem terminal_pairing (hJ : StandardTerminalPastLocality J) {P : ℝ}
    {b : C(UnitAddTorus ι, ℂ)} (hb : ∀ z, (b z).im = 0) {η : Lp (State S) 2 μ}
    (U : HeatLocalBackwardEquation.Solution J (laplace S P) (multiplier S b) 0 H η)
    (X : HeatItoProductEnergy.Trajectory J) (f err : ℝ≥0 → Lp (State S) 2 μ)
    (hf : MemLp f 2 (timeMeasure H)) (he : MemLp err 2 (timeMeasure H))
    (hX : ∀ᵐ s ∂timeMeasure H, X.drift s = ((laplace S P).compLpL 2 μ) (X.state s) + f s)
    (hN : ∀ᵐ s ∂timeMeasure H, X.noise s = ((multiplier S b).compLpL 2 μ) (X.state s) + err s) :
    inner ℝ (X.state H) η = inner ℝ (X.state 0) (HeatBackwardDriver.state H η U.drift 0) +
      (∫ s, inner ℝ (f s) (HeatBackwardDriver.state H η U.drift s) ∂timeMeasure H) +
      ∫ s, inner ℝ (err s) (HeatBackwardEquationEnergy.slice U.noise s) ∂timeMeasure H := by
  let Y := HeatBackwardProductTrajectory.trajectory U
  have hA := adjoint_lift_eq (μ := μ) (laplace S P) (HeatTorusGalerkinCompression.laplace_symmetric S P)
  have hM := adjoint_lift_eq (μ := μ) (multiplier S b) (HeatTorusGalerkinCompression.multiplier_symmetric S b hb)
  have hY : ∀ᵐ s ∂timeMeasure H, Y.drift s =
      -(((laplace S P).compLpL 2 μ).adjoint (Y.state s)) -
        ((multiplier S b).compLpL 2 μ).adjoint (Y.noise s) := by
    filter_upwards [HeatBackwardEquationEnergy.drift_slices U] with s hs
    change -HeatBackwardEquationEnergy.slice U.drift s = _
    rw [hA, hM, hs, neg_add, sub_eq_add_neg]
    rfl
  have h := HeatItoProductEnergy.terminal_duality hJ X Y ((laplace S P).compLpL 2 μ)
    ((multiplier S b).compLpL 2 μ) f err hf he hX hY hN
  have ht : Y.state H = η := U.endpoint
  rw [ht] at h
  exact h

end Pairing

section NoiseBound

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0, ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable
local instance : MeasurableSpace (HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
local notation "J" => fun H S => HeatTerminalNaturality.integral F μ H
  (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar H)

def noiseBound (b : C(UnitAddTorus ι, ℂ)) (C decay : ℝ) (H : ℝ≥0) : ℝ :=
  2 + 4 * ‖b‖ ^ 2 * (H : ℝ) *
    Real.exp ((HeatGalerkinWeightedDrift.coefficientBound ι C decay) ^ 2 * (H : ℝ))

theorem noise_energy_le {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ))
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    {S : Finset (ι → ℤ)} {H : ℝ≥0} {η : Lp (State S) 2 μ}
    (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η) :
    (∫ s, ‖HeatBackwardEquationEnergy.slice U.noise s‖ ^ 2 ∂timeMeasure H) ≤
      noiseBound b C decay H * ‖η‖ ^ 2 := by
  let β := HeatGalerkinWeightedDrift.coefficientBound ι C decay
  let M := Real.exp (β ^ 2 * (H : ℝ))
  have hJ : StandardTerminalPastLocality (J H S) :=
    HeatTerminalNaturality.locality F μ H (HeatTorusGalerkinBackward.basis S)
      (HeatCanonicalNative.scalar H) (HeatCanonicalNative.locality H)
  have hs (t : ℝ≥0) (ht : t ≤ H) : ‖HeatBackwardDriver.state H η U.drift t‖ ^ 2 ≤ M * ‖η‖ ^ 2 := by
    have h := HeatTorusAnalyticInterpolation.energy_le hP hC ha b hdec S ht le_rfl U
    rw [U.endpoint] at h
    refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (sq_nonneg _))
    exact mul_le_mul_of_nonneg_left (sub_le_self _ t.property) (sq_nonneg _)
  have hc := HeatBackwardProductTrajectory.noise_energy_le hJ U
    (HeatTorusGalerkinCompression.laplace_nonpos S P) hs
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (HeatTorusGalerkinCompression.multiplier_norm S b) 2
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  change 2 + 4 * ‖multiplier S b‖ ^ 2 * (H : ℝ) * M ≤ 2 + 4 * ‖b‖ ^ 2 * (H : ℝ) * M
  gcongr

/-- The projected diffusion defect is paired against a noise energy bound
with a constant that is uniform in the Galerkin frequency set. -/
theorem defect_pairing_sq_le {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ))
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    {S : Finset (ι → ℤ)} {H : ℝ≥0} {η : Lp (State S) 2 μ}
    (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η)
    (err : ℝ≥0 → Lp (State S) 2 μ) (he : MemLp err 2 (timeMeasure H)) :
    (∫ s, inner ℝ (err s) (HeatBackwardEquationEnergy.slice U.noise s) ∂timeMeasure H) ^ 2 ≤
      (∫ s, ‖err s‖ ^ 2 ∂timeMeasure H) * (noiseBound b C decay H * ‖η‖ ^ 2) := by
  let : MeasurableSpace (Lp (State S) 2 μ) := borel _
  let : BorelSpace (Lp (State S) 2 μ) := ⟨rfl⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let : SecondCountableTopology (Lp (State S) 2 μ) := Lp.SecondCountableTopology
  have hZ : MemLp (HeatBackwardEquationEnergy.slice U.noise) 2 (timeMeasure H) :=
    (HeatBackwardProductTrajectory.trajectory U).noise_square
  exact (HeatIntegralCauchy.inner_square (timeMeasure H) _ _ he hZ).trans
    (mul_le_mul_of_nonneg_left (noise_energy_le hP hC ha b hdec U) (integral_nonneg fun _ => sq_nonneg _))

/-- The actual linear diffusion error operator of Fourier truncation. -/
def diffusionResidual (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) :
    HeatTorusFourier.State ι →L[ℝ] State S :=
  let A := (HeatTorusGalerkinProjection.analysis S).restrictScalars ℝ
  A.comp (HeatTorusGalerkinCompression.fullMultiplier b) - (multiplier S b).comp A

/-- In terminal duality the actual Galerkin diffusion residual is controlled
by the time integral of the discarded forward-state energy. -/
theorem projected_defect_pairing_sq_le {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ))
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    {S : Finset (ι → ℤ)} {H : ℝ≥0} {η : Lp (State S) 2 μ}
    (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η)
    (X : ℝ≥0 → Lp (HeatTorusFourier.State ι) 2 μ) (hX : MemLp X 2 (timeMeasure H)) :
    let P₀ := ((HeatTorusGalerkinProjection.project S).restrictScalars ℝ).compLpL 2 μ
    let R := (diffusionResidual S b).compLpL 2 μ
    (∫ s, inner ℝ (R (X s)) (HeatBackwardEquationEnergy.slice U.noise s) ∂timeMeasure H) ^ 2 ≤
      (‖b‖ ^ 2 * (∫ s, ‖X s - P₀ (X s)‖ ^ 2 ∂timeMeasure H)) * (noiseBound b C decay H * ‖η‖ ^ 2) := by
  intro P₀ R
  let ν := timeMeasure H
  let r (s : ℝ≥0) := R (X s)
  let Q (s : ℝ≥0) := X s - P₀ (X s)
  have hr : MemLp r 2 ν := R.lipschitzWith.comp_memLp (map_zero R) hX
  have hQ : MemLp Q 2 ν := hX.sub (P₀.lipschitzWith.comp_memLp (map_zero P₀) hX)
  have hn (s : ℝ≥0) : ‖r s‖ ≤ ‖b‖ * ‖Q s‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(diffusionResidual S b).coeFn_compLpL (X s),
      ((HeatTorusGalerkinProjection.project S).restrictScalars ℝ).coeFn_compLpL (X s),
      Lp.coeFn_sub (X s) (P₀ (X s))] with ω hrω hpω hQω
    change ‖r s ω‖ ≤ ‖b‖ * ‖Q s ω‖
    change r s ω = diffusionResidual S b (X s ω) at hrω
    change P₀ (X s) ω = HeatTorusGalerkinProjection.project S (X s ω) at hpω
    change Q s ω = (X s ω) - P₀ (X s) ω at hQω
    rw [hrω, hQω, hpω]
    exact HeatTorusGalerkinCompression.diffusion_defect_norm S b (X s ω)
  have hi : (∫ s, ‖r s‖ ^ 2 ∂ν) ≤ ‖b‖ ^ 2 * ∫ s, ‖Q s‖ ^ 2 ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono hr.norm.integrable_sq (hQ.norm.integrable_sq.const_mul _)
    intro s
    exact (pow_le_pow_left₀ (norm_nonneg _) (hn s) 2).trans_eq (mul_pow ..)
  exact (defect_pairing_sq_le hP hC ha b hdec U r hr).trans
    (mul_le_mul_of_nonneg_right hi (mul_nonneg (by unfold noiseBound; positivity) (sq_nonneg _)))

end NoiseBound

end HeatTorusGalerkinTerminalDuality

#print axioms HeatTorusGalerkinTerminalDuality.terminal_pairing
#print axioms HeatTorusGalerkinTerminalDuality.noise_energy_le
#print axioms HeatTorusGalerkinTerminalDuality.defect_pairing_sq_le
#print axioms HeatTorusGalerkinTerminalDuality.projected_defect_pairing_sq_le
