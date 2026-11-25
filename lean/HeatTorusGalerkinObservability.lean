import HeatAnalyticTimeObservation
import HeatGevreyPeriodicHolomorphic
import HeatTorusAnalyticInterpolation
import HeatTorusObservedMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatTorusGalerkinObservability

open MeasureTheory Set SHE SHE.PredictableL2 UnitAddTorus
open HeatGevreyFourierExtension (weight)
open HeatTorusGalerkinBackward (State laplace multiplier)
open HeatTorusObservedPolynomial (observedEnergy)
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
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable
local instance : MeasurableSpace (HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (HilbertColumns.Space Unit ℝ) := ⟨rfl⟩

local notation "J" => fun H S => HeatTerminalNaturality.integral F μ H
  (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar H)

private theorem cost_eq {P C decay ρ δ : ℝ} (hP : 0 < P) (hδ : 0 < δ) :
    HeatTorusAnalyticInterpolation.smoothingCost ι P C decay ρ δ =
      (2 : ℝ) ^ Fintype.card ι *
        Real.exp ((HeatGalerkinWeightedDrift.coefficientBound ι C decay) ^ 2 * δ +
          ((Fintype.card ι : ℝ) * (ρ / (2 * Real.pi / P)) ^ 2 / 2) / δ) := by
  unfold HeatTorusAnalyticInterpolation.smoothingCost
  congr 2
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (2 * Real.pi / P : ℝ) ≠ 0 := ne_of_gt (div_pos (by positivity) hP)
  field_simp [hδ.ne', hc]

/-- A time-integrated observability inequality for the actual finite Fourier
adjoint on canonical Wiener space. The constant is common to every finite
set of Galerkin modes and every adapted square-integrable terminal datum. -/
theorem observable {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (hdecay : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ))
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty)
    {H : ℝ≥0} (hH : 0 < H) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (S : Finset (ι → ℤ)) {η : Lp (State S) 2 μ}
      (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η),
      ‖HeatBackwardDriver.state H η U.drift 0‖ ^ 2 ≤
        L * ∫ t, observedEnergy O (HeatBackwardDriver.state H η U.drift t) ∂timeMeasure H := by
  let ρ := decay / 2
  have hρ : 0 < ρ := half_pos hdecay
  obtain ⟨D, K, θ, hD, hK, hθ, hθ₁, htwo⟩ :=
    HeatTorusAnalyticInterpolation.two_time hP hC hdecay hρ (le_refl (decay / 2)) b hdec hO hOne
  let β := HeatGalerkinWeightedDrift.coefficientBound ι C decay
  let M := Real.exp (β ^ 2 * (H : ℝ))
  let N := K ^ 2 * (2 : ℝ) ^ Fintype.card ι * M
  let B := (Fintype.card ι : ℝ) * (ρ / (2 * Real.pi / P)) ^ 2 / 2
  have hM : 0 ≤ M := Real.exp_nonneg _
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨L, hL, hobs⟩ := HeatAnalyticTimeObservation.integrated hH hθ hθ₁ hM
    (mul_nonneg hD.le (Real.rpow_nonneg hN (1 - θ))) (mul_nonneg hB (sub_nonneg.mpr hθ₁.le))
  refine ⟨L, hL, fun S η U => ?_⟩
  let X (t : ℝ≥0) := HeatBackwardDriver.state H η U.drift t
  let E (t : ℝ≥0) := ‖X t‖ ^ 2
  let Q (t : ℝ≥0) := observedEnergy O (X t)
  have hExp {s t : ℝ≥0} (ht : t ≤ H) : Real.exp (β ^ 2 * ((t : ℝ) - s)) ≤ M := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have ht' : (t : ℝ) ≤ H := by exact_mod_cast ht
    exact (sub_le_self _ s.property).trans ht'
  apply hobs E Q (fun _ => sq_nonneg _) (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (HeatTorusObservedMap.integrable_energy O (HeatProjectedBackwardEnergy.mem_state U))
  · intro s t hst ht
    exact (HeatTorusAnalyticInterpolation.energy_le hP hC hdecay b hdec S hst ht U).trans
      (mul_le_mul_of_nonneg_right (hExp ht) (sq_nonneg _))
  · intro s t hst ht
    let δ := (t : ℝ) - s
    have hδ : 0 < δ := sub_pos.mpr (by exact_mod_cast hst)
    have hbound : K ^ 2 * HeatTorusAnalyticInterpolation.smoothingCost ι P C decay ρ δ * E t ≤
        N * Real.exp (B / δ) * E t := by
      rw [cost_eq hP hδ]
      change K ^ 2 * ((2 : ℝ) ^ Fintype.card ι * Real.exp (β ^ 2 * δ + B / δ)) * E t ≤ _
      rw [Real.exp_add]
      calc
        _ = (K ^ 2 * (2 : ℝ) ^ Fintype.card ι * Real.exp (β ^ 2 * δ)) * Real.exp (B / δ) * E t := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hExp ht) (by positivity)) (Real.exp_nonneg _)) (sq_nonneg _)
    have h := htwo S hst ht U
    change E s ≤ D * (K ^ 2 * HeatTorusAnalyticInterpolation.smoothingCost ι P C decay ρ δ * E t) ^ (1 - θ) *
      (Q s) ^ θ at h
    calc
      E s ≤ D * (N * Real.exp (B / δ) * E t) ^ (1 - θ) * (Q s) ^ θ := h.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by unfold HeatTorusAnalyticInterpolation.smoothingCost E; positivity)
            hbound (sub_nonneg.mpr hθ₁.le)) hD.le)
          (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _))
      _ = _ := by
        rw [Real.mul_rpow (mul_nonneg hN (Real.exp_nonneg _)) (sq_nonneg _),
          Real.mul_rpow hN (Real.exp_nonneg _), ← Real.exp_mul]
        rw [show B / δ * (1 - θ) = B * (1 - θ) / δ by ring]
        ring

/-- The Galerkin observability estimate under the paper's mixed factorial
derivative bound, with the observation set on the physical-period torus. -/
theorem observable_gevrey_one [Nonempty ι] [DecidableEq ι] {P : ℝ} (hP : 0 < P)
    (b : (ι → AddCircle P) → ℝ) (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0))
    (hD : ∀ (l : List ι) x, |HeatGevreyProduct.mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x| ≤
      C * ρ ^ l.length * (l.length.factorial : ℝ))
    {O : Set (ι → AddCircle P)} (hO : IsOpen O) (hOne : O.Nonempty)
    {H : ℝ≥0} (hH : 0 < H) :
    ∃ g : C(UnitAddTorus ι, ℂ), (∀ x, g x = (b (HeatTorusInitialData.rescale hP x) : ℂ)) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ (S : Finset (ι → ℤ)) {η : Lp (State S) 2 μ}
        (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S g) 0 H η),
        ‖HeatBackwardDriver.state H η U.drift 0‖ ^ 2 ≤ L *
          ∫ t, observedEnergy (HeatTorusInitialData.rescale hP ⁻¹' O)
            (HeatBackwardDriver.state H η U.drift t) ∂timeMeasure H := by
  obtain ⟨g, hg, a, ha, hdec⟩ :=
    HeatGevreyPeriodicHolomorphic.exists_coefficient_decay hP b C ρ hC hρ hb hD
  have hOpen := hO.preimage (HeatTorusInitialData.rescale hP).continuous
  have hNonempty : (HeatTorusInitialData.rescale hP ⁻¹' O).Nonempty := by
    obtain ⟨x, hx⟩ := hOne
    exact ⟨(HeatTorusInitialData.rescale hP).symm x, by simpa using hx⟩
  exact ⟨g, hg, observable hP (by positivity) ha g hdec hOpen hNonempty hH⟩

end HeatTorusGalerkinObservability

#print axioms HeatTorusGalerkinObservability.observable
#print axioms HeatTorusGalerkinObservability.observable_gevrey_one
