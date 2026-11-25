import HeatTorusMildProjection
import HeatTorusSobolevFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace HeatTorusProjectedEnergy

open Filter MeasureTheory SHE SHE.PredictableL2
open HeatTorusFourier (frequencySquared)
open HeatTorusGalerkinBackward (State laplace laplace_apply)
open scoped NNReal ENNReal ComplexConjugate

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

/-- Dirichlet energy in a finite Fourier projection. -/
def spatial (S : Finset (ι → ℤ)) (P : ℝ) (x : State S) : ℝ :=
  ∑ k : ↥S, frequencySquared P k.val * ‖x k‖ ^ 2

theorem spatial_eq_neg_pairing (S : Finset (ι → ℤ)) (P : ℝ) (x : State S) :
    spatial S P x = -inner ℝ (laplace S P x) x := by
  change spatial S P x = -(inner ℂ (laplace S P x) x).re
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change spatial S P x = -(∑ k : ↥S, x k * star (laplace S P x k)).re
  rw [show (∑ k : ↥S, x k * star (laplace S P x k)).re =
    ∑ k : ↥S, (x k * star (laplace S P x k)).re from map_sum Complex.reCLM _ _,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [laplace_apply]
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem lp_pairing (S : Finset (ι → ℤ)) (P : ℝ) (μ : Measure Ω) (x : Lp (State S) 2 μ) :
    -inner ℝ ((laplace S P).compLpL 2 μ x) x = ∫ ω, spatial S P (x ω) ∂μ := by
  rw [L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(laplace S P).coeFn_compLpL x] with ω hω
  rw [hω, spatial_eq_neg_pairing]

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {T : ℝ≥0} {S : Finset (ι → ℤ)} {P : ℝ}
  {I : StandardTerminalIto (C := State S) (E := State S) F μ T}

/-- The forward Itô energy estimate bounds the spatial derivative energy
of the finite projection by its initial, forcing, state and diffusion energies. -/
theorem bound (hI : StandardTerminalPastLocality I) (X : HeatItoProductEnergy.Trajectory I)
    (f : ℝ≥0 → Lp (State S) 2 μ) (hf : MemLp f 2 (timeMeasure T))
    (hd : ∀ᵐ t ∂timeMeasure T, X.drift t = ((laplace S P).compLpL 2 μ) (X.state t) + f t) :
    2 * (∫ t, ∫ ω, spatial S P (X.state t ω) ∂μ ∂timeMeasure T) ≤
      ‖X.state 0‖ ^ 2 + (∫ t, ‖f t‖ ^ 2 + ‖X.state t‖ ^ 2 ∂timeMeasure T) +
        ∫ t, ‖X.noise t‖ ^ 2 ∂timeMeasure T := by
  let L := (laplace S P).compLpL 2 μ
  have hL := L.lipschitzWith.comp_memLp (map_zero L) X.state_square
  have hLpair : Integrable (fun t => inner ℝ (L (X.state t)) (X.state t)) (timeMeasure T) :=
    HeatL2Integrability.inner (timeMeasure T) _ _ hL X.state_square
  have hfpair := HeatL2Integrability.inner (timeMeasure T) _ _ hf X.state_square
  have hsum : (fun t => inner ℝ (X.drift t) (X.state t)) =ᵐ[timeMeasure T]
      fun t => inner ℝ (L (X.state t)) (X.state t) + inner ℝ (f t) (X.state t) := by
    filter_upwards [hd] with t ht
    rw [ht, inner_add_left]
  have he := HeatTerminalItoCompression.energy_prefix I hI le_rfl (X.state 0) X.initial_adapted X.drift
    (X.drift_square.integrable one_le_two) X.drift_adapted X.process X.state X.noise X.noise_slices X.equation
  rw [integral_congr_ae hsum, integral_add hLpair hfpair] at he
  have hfbound (t : ℝ≥0) : 2 * inner ℝ (f t) (X.state t) ≤ ‖f t‖ ^ 2 + ‖X.state t‖ ^ 2 := by
    have hcs := real_inner_le_norm (f t) (X.state t)
    nlinarith [sq_nonneg (‖f t‖ - ‖X.state t‖)]
  have hib := integral_mono (hfpair.const_mul 2) (hf.norm.integrable_sq.add X.state_square.norm.integrable_sq) hfbound
  rw [integral_const_mul] at hib
  change 2 * (∫ t, inner ℝ (f t) (X.state t) ∂timeMeasure T) ≤
    ∫ t, ‖f t‖ ^ 2 + ‖X.state t‖ ^ 2 ∂timeMeasure T at hib
  simp_rw [← lp_pairing, integral_neg]
  change 2 * -(∫ t, inner ℝ (L (X.state t)) (X.state t) ∂timeMeasure T) ≤ _
  nlinarith only [he, hib, sq_nonneg ‖X.state T‖]

end HeatTorusProjectedEnergy

#print axioms HeatTorusProjectedEnergy.lp_pairing
#print axioms HeatTorusProjectedEnergy.bound
