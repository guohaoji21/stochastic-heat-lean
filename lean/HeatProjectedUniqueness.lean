import HeatTorusProjectedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatProjectedUniqueness

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open HeatTorusGalerkinBackward (State laplace)
open scoped NNReal ENNReal

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {T : ℝ≥0} {S : Finset (ι → ℤ)} {P : ℝ}
  {I : StandardTerminalIto (C := State S) (E := State S) F μ T}

private theorem stop_sub (t : ℝ≥0) (v w : Process (E := State S) F μ T) :
    stop F μ T t (v - w) = stop F μ T t v - stop F μ T t w := by
  apply eq_sub_of_add_eq
  rw [← TwoChannelItoRows.stop_add, sub_add_cancel]

/-- Two finite projections with the same initial data and forcing can
differ only by their diffusion. The spatial Laplacian contributes a
nonpositive term in the expected energy of the difference. -/
theorem difference_bound (hI : StandardTerminalPastLocality I)
    (X Y : HeatItoProductEnergy.Trajectory I) (h0 : X.state 0 = Y.state 0)
    (f : ℝ≥0 → Lp (State S) 2 μ)
    (hX : ∀ r, X.drift r = ((laplace S P).compLpL 2 μ) (X.state r) + f r)
    (hY : ∀ r, Y.drift r = ((laplace S P).compLpL 2 μ) (Y.state r) + f r)
    (t : ℝ≥0) (ht : t ≤ T) :
    ‖X.state t - Y.state t‖ ^ 2 ≤ ∫ r, ‖X.noise r - Y.noise r‖ ^ 2 ∂timeMeasure t := by
  let Z (r : ℝ≥0) := X.state r - Y.state r
  let N (r : ℝ≥0) := X.noise r - Y.noise r
  let D (r : ℝ≥0) := X.drift r - Y.drift r
  let u := X.process - Y.process
  have hD (r : ℝ≥0) : D r = ((laplace S P).compLpL 2 μ) (Z r) := by
    dsimp only [D, Z]
    rw [hX, hY, add_sub_add_right_eq_sub, map_sub]
  have hZa : AEStronglyMeasurable[F 0] (Z 0 : Ω → State S) μ :=
    (X.initial_adapted.sub Y.initial_adapted).congr (Lp.coeFn_sub _ _).symm
  have hDa : ∀ᵐ r ∂timeMeasure T, AEStronglyMeasurable[F r] (D r : Ω → State S) μ := by
    filter_upwards [X.drift_adapted, Y.drift_adapted] with r hx hy
    exact (hx.sub hy).congr (Lp.coeFn_sub _ _).symm
  have hN : ∀ᵐ r ∂timeMeasure T, (fun ω => u (r, ω)) =ᵐ[μ] N r := by
    filter_upwards [Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub X.process Y.process)),
      X.noise_slices, Y.noise_slices] with r h₀ hx hy
    filter_upwards [h₀, hx, hy, Lp.coeFn_sub (X.noise r) (Y.noise r)] with ω h₀ hx hy h₁
    rw [h₀, h₁, Pi.sub_apply, Pi.sub_apply, hx, hy]
  have hDi := (X.drift_square.sub Y.drift_square).integrable one_le_two
  have hZ (r : ℝ≥0) (hr : r ≤ T) :
      Z r = Z 0 + HeatDeterministicPairing.cumulative (timeMeasure T) D r +
        HeatStoppedPairing.value F μ T I u r := by
    dsimp only [Z, D, u]
    rw [X.equation r hr, Y.equation r hr]
    unfold HeatDeterministicPairing.cumulative HeatStoppedPairing.value
    rw [integral_sub (X.drift_square.integrable one_le_two).integrableOn
      (Y.drift_square.integrable one_le_two).integrableOn, stop_sub, map_sub]
    abel
  have h := HeatTerminalItoCompression.energy_prefix I hI ht (Z 0) hZa D hDi hDa u Z N hN hZ
  have hdiss (r : ℝ≥0) : inner ℝ (D r) (Z r) ≤ 0 := by
    rw [hD]
    have he := HeatTorusProjectedEnergy.lp_pairing S P μ (Z r)
    have hnon : 0 ≤ ∫ ω, HeatTorusProjectedEnergy.spatial S P (Z r ω) ∂μ :=
      integral_nonneg fun ω => Finset.sum_nonneg
        (fun k _ => mul_nonneg (HeatTorusFourier.frequencySquared_nonneg P k.val) (sq_nonneg _))
    linarith only [he, hnon]
  have hi : (∫ r, inner ℝ (D r) (Z r) ∂timeMeasure t) ≤ 0 := integral_nonpos hdiss
  have hzero : Z 0 = 0 := sub_eq_zero.mpr h0
  rw [hzero, norm_zero] at h
  change ‖Z t‖ ^ 2 ≤ ∫ r, ‖N r‖ ^ 2 ∂timeMeasure t
  nlinarith only [h, hi]

end HeatProjectedUniqueness

#print axioms HeatProjectedUniqueness.difference_bound
