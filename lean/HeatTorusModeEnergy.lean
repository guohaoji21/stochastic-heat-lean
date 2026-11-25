import HeatTorusGalerkinBackward
import HeatProjectedBackwardEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatTorusModeEnergy

open Filter MeasureTheory SHE.PredictableL2
open HeatTorusGalerkinBackward (State modeProjection modeProjection_norm_sq modeProjection_inner)
open scoped NNReal ENNReal

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)

/-- Pointwise quadratic density for one complex Fourier coordinate. -/
def pointDensity (x d y : ℂ) : ℝ := 2 * ((-d) * star x).re + ‖y‖ ^ 2

theorem integral_mode_energy {S : Finset (ι → ℤ)} (k : ↥S) (X : Lp (State S) 2 μ) :
    ‖((modeProjection S k).compLpL 2 μ) X‖ ^ 2 = ∫ ω, ‖X ω k‖ ^ 2 ∂μ := by
  rw [realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [(modeProjection S k).coeFn_compLpL X] with ω hω
  rw [hω, modeProjection_norm_sq]

theorem integrable_mode_energy {S : Finset (ι → ℤ)} (k : ↥S) (X : Lp (State S) 2 μ) :
    Integrable (fun ω => ‖X ω k‖ ^ 2) μ := by
  apply (Lp.memLp (((modeProjection S k).compLpL 2 μ) X)).norm.integrable_sq.congr
  filter_upwards [(modeProjection S k).coeFn_compLpL X] with ω hω
  change ‖((modeProjection S k).compLpL 2 μ) X ω‖ ^ 2 = ‖X ω k‖ ^ 2
  rw [hω, modeProjection_norm_sq]

private theorem pointDensity_ae {S : Finset (ι → ℤ)} (k : ↥S) (X D Y : Lp (State S) 2 μ) :
    (fun ω => 2 * inner ℝ ((-((modeProjection S k).compLpL 2 μ) D : Lp (State S) 2 μ) ω)
        (((modeProjection S k).compLpL 2 μ) X ω) +
      ‖((modeProjection S k).compLpL 2 μ) Y ω‖ ^ 2) =ᵐ[μ]
      fun ω => pointDensity (X ω k) (D ω k) (Y ω k) := by
  let Q := modeProjection S k
  let L := Q.compLpL 2 μ
  filter_upwards [Q.coeFn_compLpL X, Q.coeFn_compLpL D, Q.coeFn_compLpL Y,
    Lp.coeFn_neg (L D)] with ω hx hd hy hn
  change 2 * inner ℝ ((-L D) ω) (L X ω) + ‖L Y ω‖ ^ 2 = _
  rw [hn, Pi.neg_apply, hd, hx, hy, ← map_neg, modeProjection_inner, modeProjection_norm_sq]
  rfl

theorem integrable_mode_density {S : Finset (ι → ℤ)} (k : ↥S) (X D Y : Lp (State S) 2 μ) :
    Integrable (fun ω => pointDensity (X ω k) (D ω k) (Y ω k)) μ := by
  let L := (modeProjection S k).compLpL 2 μ
  have h := ((L2.integrable_inner (𝕜 := ℝ) (-L D) (L X)).const_mul 2).add
    ((Lp.memLp (L Y)).norm.integrable_sq)
  exact h.congr (pointDensity_ae k X D Y)

theorem integral_mode_density {S : Finset (ι → ℤ)} (k : ↥S) (X D Y : Lp (State S) 2 μ) :
    (let L := (modeProjection S k).compLpL 2 μ
     2 * inner ℝ (-L D) (L X) + ‖L Y‖ ^ 2) = ∫ ω, pointDensity (X ω k) (D ω k) (Y ω k) ∂μ := by
  let L := (modeProjection S k).compLpL 2 μ
  change 2 * inner ℝ (-L D) (L X) + ‖L Y‖ ^ 2 = _
  rw [L2.inner_def, realLp_norm_sq, ← integral_const_mul,
    ← integral_add ((L2.integrable_inner (𝕜 := ℝ) (-L D) (L X)).const_mul 2)
      ((Lp.memLp (L Y)).norm.integrable_sq)]
  exact integral_congr_ae (pointDensity_ae k X D Y)

theorem sum_mode_energy {S : Finset (ι → ℤ)} (X : Lp (State S) 2 μ) :
    (∑ k : ↥S, ‖((modeProjection S k).compLpL 2 μ) X‖ ^ 2) = ‖X‖ ^ 2 := by
  simp_rw [integral_mode_energy]
  rw [← integral_finsetSum Finset.univ (fun k _ => integrable_mode_energy k X), realLp_norm_sq]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => (EuclideanSpace.norm_sq_eq _).symm

end HeatTorusModeEnergy

#print axioms HeatTorusModeEnergy.integral_mode_density
#print axioms HeatTorusModeEnergy.sum_mode_energy
