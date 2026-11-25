import HeatAffineEnergyClock
import HeatCanonicalSeparable
import HeatGalerkinWeightedDrift
import HeatTorusModeEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatTorusWeightedEnergy

open Filter MeasureTheory Set SHE SHE.PredictableL2 UnitAddTorus
open HeatAnalyticGalerkinEnergy (translationWeight translationWeight_add)
open HeatGalerkinWeightedDrift (translated coefficientBound compensation)
open HeatGevreyFourierExtension (weight)
open HeatTorusGalerkinBackward (State laplace multiplier modeProjection)
open HeatTorusModeEnergy (pointDensity)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

private def direction (v : ι → ℝ) (k : ι → ℤ) : ℝ := ∑ i, v i * (k i : ℝ)

private theorem clock_weight (v : ι → ℝ) (k : ι → ℤ) (Γ t : ℝ) :
    Real.exp ((2 * direction v k + Γ) * t) =
      Real.exp (Γ * t) * translationWeight (fun i => t * v i) k ^ 2 := by
  rw [translationWeight, ← Real.exp_nat_mul, ← Real.exp_add]
  simp only [Nat.cast_ofNat, direction]
  congr 1
  have he : ∑ i, t * v i * (k i : ℝ) = ∑ i, t * (v i * (k i : ℝ)) := by
    simp only [mul_assoc]
  rw [he, ← Finset.mul_sum]
  ring

private theorem translated_convolution (q : ι → ℝ) (S : Finset (ι → ℤ))
    (b : (ι → ℤ) → ℂ) (y : ↥S → ℂ) (k : ↥S) :
    (translationWeight q k.val : ℂ) * (∑ l : ↥S, b (k.val - l.val) * y l) =
      ∑ l : ↥S, translated q b (k.val - l.val) * ((translationWeight q l.val : ℂ) * y l) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have h := translationWeight_add q (k.val - l.val) l.val
  rw [sub_add_cancel] at h
  rw [h, Complex.ofReal_mul, translated]
  ring

private theorem scaled_density (θ freq r : ℝ) (x n y : ℂ) :
    θ ^ 2 * (pointDensity x (((-freq : ℝ) : ℂ) * x + n) y + r * ‖x‖ ^ 2) =
      (2 * freq + r) * ‖(θ : ℂ) * x‖ ^ 2 + ‖(θ : ℂ) * y‖ ^ 2 -
        2 * (((θ : ℂ) * n) * star ((θ : ℂ) * x)).re := by
  simp only [pointDensity, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

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

/-- The directionally weighted expected energy at the earlier time is
bounded by the unweighted expected energy at the later time, uniformly in
the Galerkin frequency set. -/
theorem endpoint_le {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ))
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    (S : Finset (ι → ℤ)) {H p q : ℝ≥0} (hpq : p ≤ q) (hqH : q ≤ H)
    (v : ι → ℝ) (hv : ∀ i, ((q : ℝ) - p) * |v i| ≤ decay / 2)
    {η : Lp (State S) 2 μ}
    (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η) :
    (∑ k : ↥S, translationWeight (fun i => ((p : ℝ) - q) * v i) k.val ^ 2 *
      HeatProjectedBackwardEnergy.energy (modeProjection S k) U p) ≤
      Real.exp (compensation P v (coefficientBound ι C decay) * ((q : ℝ) - p)) *
        ‖HeatBackwardDriver.state H η U.drift q‖ ^ 2 := by
  let Γ := compensation P v (coefficientBound ι C decay)
  let r (k : ↥S) := 2 * direction v k.val + Γ
  let E (k : ↥S) := HeatProjectedBackwardEnergy.energy (modeProjection S k) U
  let g (k : ↥S) := HeatProjectedBackwardEnergy.density (modeProjection S k) U
  have hJ : StandardTerminalPastLocality (J H S) :=
    HeatTerminalNaturality.locality F μ H (HeatTorusGalerkinBackward.basis S)
      (HeatCanonicalNative.scalar H) (HeatCanonicalNative.locality H)
  have hg (k : ↥S) : Integrable (g k) (timeMeasure H) :=
    HeatProjectedBackwardEnergy.integrable_density (modeProjection S k) U
  have hE (k : ↥S) (t : ℝ≥0) (ht : t ≤ H) : E k t = E k 0 + ∫ s, g k s ∂timeMeasure t :=
    HeatProjectedBackwardEnergy.energy_prefix hJ (modeProjection S k)
      (HeatTerminalNaturality.commutes F μ H (HeatTorusGalerkinBackward.basis S)
        (HeatCanonicalNative.scalar H) (modeProjection S k)) U ht
  have hw (t : ℝ≥0) (k : ↥S) :
      -(r k * (q : ℝ)) + r k * (t : ℝ) = r k * ((t : ℝ) - q) := by ring
  have hsign : ∀ᵐ t ∂timeMeasure H, t ∈ Ioc p q →
      0 ≤ ∑ k, Real.exp (-(r k * (q : ℝ)) + r k * (t : ℝ)) * (g k t + r k * E k t) := by
    filter_upwards [HeatBackwardEquationEnergy.drift_slices U] with t hdt
    intro ht
    let X := HeatBackwardDriver.state H η U.drift t
    let D := HeatBackwardEquationEnergy.slice U.drift t
    let Y := HeatBackwardEquationEnergy.slice U.noise t
    let z (i : ι) := ((t : ℝ) - q) * v i
    let θ (k : ↥S) := translationWeight z k.val
    let w (k : ↥S) := Real.exp (r k * ((t : ℝ) - q))
    have hz (i : ι) : |z i| ≤ decay / 2 := by
      have h₁ : (t : ℝ) ≤ q := by exact_mod_cast ht.2
      have h₂ : (p : ℝ) ≤ t := by exact_mod_cast ht.1.le
      dsimp only [z]
      rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr h₁), neg_sub]
      exact (mul_le_mul_of_nonneg_right (sub_le_sub_left h₂ _) (abs_nonneg _)).trans (hv i)
    have hD : ∀ᵐ ω ∂μ, D ω = laplace S P (X ω) + multiplier S b (Y ω) := by
      change D = ((laplace S P).compLpL 2 μ) X + ((multiplier S b).compLpL 2 μ) Y at hdt
      filter_upwards [Lp.coeFn_add (((laplace S P).compLpL 2 μ) X) (((multiplier S b).compLpL 2 μ) Y),
        (laplace S P).coeFn_compLpL X, (multiplier S b).coeFn_compLpL Y] with ω h₁ h₂ h₃
      rw [hdt, h₁, Pi.add_apply, h₂, h₃]
    let f (k : ↥S) (ω : C(ℝ≥0, ℝ)) := pointDensity (X ω k) (D ω k) (Y ω k) + r k * ‖X ω k‖ ^ 2
    have hdens (k : ↥S) : Integrable (fun ω => pointDensity (X ω k) (D ω k) (Y ω k)) μ :=
      HeatTorusModeEnergy.integrable_mode_density k X D Y
    have hnorm (k : ↥S) : Integrable (fun ω => r k * ‖X ω k‖ ^ 2) μ :=
      (HeatTorusModeEnergy.integrable_mode_energy k X).const_mul (r k)
    have hf (k : ↥S) : Integrable (f k) μ := (hdens k).add (hnorm k)
    have hterm (k : ↥S) : g k t + r k * E k t = ∫ ω, f k ω ∂μ := by
      change (2 * inner ℝ (-((modeProjection S k).compLpL 2 μ) D)
          (((modeProjection S k).compLpL 2 μ) X) + ‖((modeProjection S k).compLpL 2 μ) Y‖ ^ 2) +
          r k * ‖((modeProjection S k).compLpL 2 μ) X‖ ^ 2 = _
      rw [HeatTorusModeEnergy.integral_mode_density k X D Y, HeatTorusModeEnergy.integral_mode_energy,
        ← integral_const_mul, ← integral_add (hdens k) (hnorm k)]
    simp_rw [hw, hterm]
    change 0 ≤ ∑ k, w k * ∫ ω, f k ω ∂μ
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum Finset.univ (fun k _ => (hf k).const_mul (w k))]
    apply integral_nonneg_of_ae
    filter_upwards [hD] with ω hω
    let x' (k : ↥S) := (θ k : ℂ) * X ω k
    let y' (k : ↥S) := (θ k : ℂ) * Y ω k
    let N (k : ↥S) := ∑ l : ↥S, mFourierCoeff b (k.val - l.val) * Y ω l
    let N' (k : ↥S) := ∑ l : ↥S, translated z (mFourierCoeff b) (k.val - l.val) * y' l
    let e := Real.exp (Γ * ((t : ℝ) - q))
    have hcoord (k : ↥S) : D ω k = ((-HeatTorusFourier.frequencySquared P k.val : ℝ) : ℂ) * X ω k + N k := by
      rw [hω]
      change laplace S P (X ω) k + multiplier S b (Y ω) k = _
      rw [HeatTorusGalerkinBackward.laplace_apply, HeatTorusGalerkinBackward.multiplier_apply]
    have hscale (k : ↥S) : (θ k : ℂ) * N k = N' k :=
      translated_convolution z S (mFourierCoeff b) (Y ω) k
    have h := HeatGalerkinWeightedDrift.energy_nonneg hP hC ha (mFourierCoeff b) hdec z v hz S x' y'
    have hfactor (k : ↥S) : w k = e * θ k ^ 2 := clock_weight v k.val Γ _
    calc
      0 ≤ e * (∑ k : ↥S, ((2 * HeatTorusFourier.frequencySquared P k.val + r k) * ‖x' k‖ ^ 2 +
          ‖y' k‖ ^ 2 - 2 * (N' k * star (x' k)).re)) := by
        apply mul_nonneg (Real.exp_nonneg _)
        simpa only [r, direction, N', add_assoc] using h
      _ = ∑ k, w k * f k ω := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [f]
        rw [hfactor, mul_assoc, hcoord, scaled_density, hscale]
  have h := HeatAffineEnergyClock.endpoint_le hpq hqH (fun k => -(r k * (q : ℝ))) r E g hg hE hsign
  simp_rw [hw] at h
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at h
  have hsum : (∑ k : ↥S, E k q) = ‖HeatBackwardDriver.state H η U.drift q‖ ^ 2 :=
    HeatTorusModeEnergy.sum_mode_energy _
  have hweight (k : ↥S) : Real.exp (r k * ((p : ℝ) - q)) = Real.exp (Γ * ((p : ℝ) - q)) *
      translationWeight (fun i => ((p : ℝ) - q) * v i) k.val ^ 2 := clock_weight v k.val Γ _
  simp_rw [hweight, mul_assoc, ← Finset.mul_sum, hsum] at h
  have hrev : Real.exp (Γ * ((p : ℝ) - q)) = (Real.exp (Γ * ((q : ℝ) - p)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hrev, ← div_eq_inv_mul] at h
  simpa only [mul_comm] using (div_le_iff₀ (Real.exp_pos _)).mp h

/-- Analytic Fourier energy on the full set of Galerkin modes. The radius is
fixed across truncations, and the compensation depends on the time gap
through the speed of the translation. -/
theorem analytic_energy_le {P C decay ρ : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (hρ : 0 ≤ ρ) (hρa : ρ ≤ decay / 2) (b : C(UnitAddTorus ι, ℂ))
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * weight k))
    (S : Finset (ι → ℤ)) {H p q : ℝ≥0} (hpq : p < q) (hqH : q ≤ H)
    {η : Lp (State S) 2 μ}
    (U : HeatLocalBackwardEquation.Solution (J H S) (laplace S P) (multiplier S b) 0 H η) :
    (∑ k : ↥S, Real.exp (2 * ρ * weight k.val) * HeatProjectedBackwardEnergy.energy (modeProjection S k) U p) ≤
      (2 : ℝ) ^ Fintype.card ι *
        (Real.exp (((coefficientBound ι C decay) ^ 2 +
          ∑ _ : ι, (ρ / ((q : ℝ) - p) / (2 * Real.pi / P)) ^ 2 / 2) * ((q : ℝ) - p)) *
          ‖HeatBackwardDriver.state H η U.drift q‖ ^ 2) := by
  classical
  let E (k : ↥S) := HeatProjectedBackwardEnergy.energy (modeProjection S k) U p
  let E₀ (k : ι → ℤ) := if hk : k ∈ S then E ⟨k, hk⟩ else 0
  let X (k : ι → ℤ) : ℂ := (Real.sqrt (E₀ k) : ℝ)
  let sign (ε : ι → Bool) (i : ι) : ℝ := if ε i then 1 else -1
  have hE₀ (k : ι → ℤ) : 0 ≤ E₀ k := by
    unfold E₀
    split <;> simp [E, HeatProjectedBackwardEnergy.energy]
  have hX (k : ι → ℤ) : ‖X k‖ ^ 2 = E₀ k := by
    rw [show X k = (Real.sqrt (E₀ k) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hE₀ k)]
  have hcomb := HeatAnalyticGalerkinEnergy.weighted_energy_le_sum_signs ρ S X
  simp only [hX] at hcomb
  change (∑ k ∈ S, Real.exp (2 * ρ * weight k) * E₀ k) ≤
    ∑ ε : ι → Bool, ∑ k ∈ S, Real.exp (2 * ρ * direction (sign ε) k) * E₀ k at hcomb
  have hval (k : ↥S) : E₀ k.val = E k := dite_eq_left k.property
  simp only [← Finset.sum_coe_sort S, hval] at hcomb
  let δ := (q : ℝ) - p
  let speed := ρ / δ
  let v (ε : ι → Bool) (i : ι) := -speed * sign ε i
  let c := 2 * Real.pi / P
  let Γ := (coefficientBound ι C decay) ^ 2 + ∑ _ : ι, (speed / c) ^ 2 / 2
  have hδ : 0 < δ := sub_pos.mpr (by exact_mod_cast hpq)
  have hspeed : 0 ≤ speed := div_nonneg hρ hδ.le
  have hscale : δ * speed = ρ := by rw [mul_comm]; exact div_mul_cancel₀ _ hδ.ne'
  have hvabs (ε : ι → Bool) (i : ι) : |v ε i| = speed := by
    have hs : |sign ε i| = 1 := by cases h : ε i <;> simp [sign, h]
    change |-speed * sign ε i| = speed
    rw [abs_mul, abs_neg, abs_of_nonneg hspeed, hs, mul_one]
  have hv (ε : ι → Bool) (i : ι) : ((q : ℝ) - p) * |v ε i| ≤ decay / 2 := by
    change δ * |v ε i| ≤ decay / 2
    rwa [hvabs, hscale]
  have hshift (ε : ι → Bool) (i : ι) : ((p : ℝ) - q) * v ε i = ρ * sign ε i := by
    change ((p : ℝ) - q) * (-speed * sign ε i) = _
    rw [show (p : ℝ) - q = -δ by dsimp only [δ]; ring,
      show -δ * (-speed * sign ε i) = (δ * speed) * sign ε i by ring, hscale]
  have hweight (ε : ι → Bool) (k : ι → ℤ) :
      translationWeight (fun i => ((p : ℝ) - q) * v ε i) k ^ 2 =
        Real.exp (2 * ρ * direction (sign ε) k) := by
    rw [translationWeight, ← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat, hshift, mul_assoc, direction, Finset.mul_sum]
  have hcomp (ε : ι → Bool) : compensation P (v ε) (coefficientBound ι C decay) = Γ := by
    have hin (i : ι) : (v ε i / c) ^ 2 = (speed / c) ^ 2 := calc
      _ = (|v ε i| / c) ^ 2 := by simp only [div_pow, sq_abs]
      _ = _ := by rw [hvabs]
    change (coefficientBound ι C decay) ^ 2 + (∑ i, (v ε i / c) ^ 2 / 2) = Γ
    simp only [hin, Γ]
  calc
    (∑ k : ↥S, Real.exp (2 * ρ * weight k.val) * E k) ≤
        ∑ ε : ι → Bool, ∑ k : ↥S, Real.exp (2 * ρ * direction (sign ε) k.val) * E k := hcomb
    _ ≤ ∑ _ : ι → Bool, Real.exp (Γ * δ) * ‖HeatBackwardDriver.state H η U.drift q‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro ε _
      simpa only [hweight, hcomp, E, δ] using endpoint_le hP hC ha b hdec S hpq.le hqH (v ε) (hv ε) U
    _ = _ := by simp [Γ, speed, c, δ]

end HeatTorusWeightedEnergy

#print axioms HeatTorusWeightedEnergy.endpoint_le
#print axioms HeatTorusWeightedEnergy.analytic_energy_le
