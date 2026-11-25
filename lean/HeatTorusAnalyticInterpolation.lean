import HeatTorusObservedPolynomial
import HeatTorusWeightedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace HeatTorusAnalyticInterpolation

open MeasureTheory SHE SHE.PredictableL2 UnitAddTorus Set
open HeatTorusGalerkinBackward (State laplace multiplier modeProjection)
open HeatTorusObservedPolynomial (observedEnergy)
open HeatGevreyFourierExtension (weight)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0, ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (HilbertColumns.Space Unit ℝ) := ⟨rfl⟩

local notation "J" => fun H S => HeatTerminalNaturality.integral F μ H
  (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar H)

/-- The common analytic energy bound on Galerkin spaces at a time gap δ. -/
def smoothingCost (ι : Type*) [Fintype ι] (P C decay ρ δ : ℝ) : ℝ :=
  (2 : ℝ) ^ Fintype.card ι *
    Real.exp (((HeatGalerkinWeightedDrift.coefficientBound ι C decay) ^ 2 +
      ∑ _ : ι, (ρ / δ / (2 * Real.pi / P)) ^ 2 / 2) * δ)

/-- The unweighted estimate propagates energy backwards between the two
times, with a constant independent of the Galerkin frequency set. -/
theorem energy_le {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ)) (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    (S : Finset (ι → ℤ)) {H p q : ℝ≥0} (hpq : p ≤ q) (hqH : q ≤ H)
    {η : Lp (State S) 2 μ}
    (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η) :
    ‖HeatBackwardDriver.state H η U.drift p‖ ^ 2 ≤
      Real.exp ((HeatGalerkinWeightedDrift.coefficientBound ι C decay) ^ 2 * ((q : ℝ) - p)) *
        ‖HeatBackwardDriver.state H η U.drift q‖ ^ 2 := by
  have hv (i : ι) : ((q : ℝ) - p) * |(0 : ℝ)| ≤ decay / 2 := by
    simp only [abs_zero, mul_zero]
    positivity
  have h := HeatTorusWeightedEnergy.endpoint_le hP hC ha b hdec S hpq hqH (fun _ => 0) hv U
  rw [← HeatTorusModeEnergy.sum_mode_energy (HeatBackwardDriver.state H η U.drift p)]
  simpa [HeatAnalyticGalerkinEnergy.translationWeight, HeatGalerkinWeightedDrift.compensation,
    HeatProjectedBackwardEnergy.energy] using h

/-- The expected adjoint state energy at the observation time is controlled
by a power of the open-set observation and a power of a later state energy.
All constants are independent of the finite frequency set. -/
theorem two_time {P C decay ρ : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (hρ : 0 < ρ) (hρa : ρ ≤ decay / 2) (b : C(UnitAddTorus ι, ℂ))
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ D K θ : ℝ, 0 < D ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (S : Finset (ι → ℤ)) {H p q : ℝ≥0}, p < q → q ≤ H →
        ∀ {η : Lp (State S) 2 μ}
          (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η),
          let X := HeatBackwardDriver.state H η U.drift p
          let Y := HeatBackwardDriver.state H η U.drift q
          ‖X‖ ^ 2 ≤ D * (K ^ 2 * smoothingCost ι P C decay ρ ((q : ℝ) - p) * ‖Y‖ ^ 2) ^ (1 - θ) *
            (observedEnergy O X) ^ θ := by
  obtain ⟨D, K, θ, hD, hK, hθ, hθ₁, hi⟩ :=
    HeatTorusObservedPolynomial.spatial_interpolation («μ» := μ) hO hOne hρ
  refine ⟨D, K, θ, hD, hK, hθ, hθ₁, ?_⟩
  intro S H p q hpq hqH η U X Y
  let A := smoothingCost ι P C decay ρ ((q : ℝ) - p)
  let e (k : ↥S) := ‖((modeProjection S k).compLpL 2 μ) X‖ ^ 2
  have hA : 0 < A := by unfold A smoothingCost; positivity
  have hweighted : (∑ k : ↥S, Real.exp (2 * ρ * weight k.val) * e k) ≤ A * ‖Y‖ ^ 2 := by
    simpa only [e, X, Y, A, smoothingCost, HeatProjectedBackwardEnergy.energy, mul_assoc] using
      HeatTorusWeightedEnergy.analytic_energy_le hP hC ha hρ.le hρa b hdec S hpq hqH U
  by_cases hzero : ‖Y‖ = 0
  · have hle : ‖X‖ ^ 2 ≤ ∑ k : ↥S, Real.exp (2 * ρ * weight k.val) * e k := by
      rw [← HeatTorusModeEnergy.sum_mode_energy X]
      apply Finset.sum_le_sum
      intro k _
      exact le_mul_of_one_le_left (sq_nonneg _)
        (Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hρ.le) (HeatGevreyFourierExtension.weight_nonneg _)))
    simpa only [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
      Real.zero_rpow (sub_ne_zero.mpr hθ₁.ne')] using hle.trans hweighted
  have hY : 0 < ‖Y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  let M := Real.sqrt (A * ‖Y‖ ^ 2)
  have hM : 0 < M := Real.sqrt_pos.mpr (mul_pos hA (pow_pos hY _))
  have hM₂ : M ^ 2 = A * ‖Y‖ ^ 2 := Real.sq_sqrt (mul_nonneg hA.le (sq_nonneg _))
  have h := hi S X M hM (by rwa [hM₂])
  let W := (M * K) ^ 2
  have hW : 0 < W := pow_pos (mul_pos hM hK) _
  have hWval : W = K ^ 2 * A * ‖Y‖ ^ 2 := by
    dsimp only [W]
    rw [mul_pow, hM₂]
    ring
  have hobs : 0 ≤ observedEnergy O X := integral_nonneg fun _ => sq_nonneg _
  change ‖X‖ ^ 2 ≤ D * (K ^ 2 * A * ‖Y‖ ^ 2) ^ (1 - θ) * (observedEnergy O X) ^ θ
  rw [← hWval, Real.rpow_sub hW, Real.rpow_one]
  change ‖X‖ ^ 2 ≤ D * W * ((observedEnergy O X / W) ^ θ) at h
  rw [Real.div_rpow hobs hW.le] at h
  convert h using 1 <;> ring

end HeatTorusAnalyticInterpolation

#print axioms HeatTorusAnalyticInterpolation.two_time
#print axioms HeatTorusAnalyticInterpolation.energy_le
