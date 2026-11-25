import HeatTorusGalerkinBackward

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace HeatTorusGalerkinProjection

open Filter MeasureTheory UnitAddTorus
open scoped Classical ENNReal Topology

variable {ι : Type*} [Fintype ι]

local notation "Full" => HeatTorusFourier.State ι
abbrev Finite (S : Finset (ι → ℤ)) := HeatTorusGalerkinBackward.State S

/-- Reconstruct a finite Fourier vector in the full torus state space. -/
def synthesis (S : Finset (ι → ℤ)) : Finite S →L[ℂ] Full :=
  ∑ k : ↥S, (EuclideanSpace.proj k).smulRight (mFourierLp 2 k.val)

theorem synthesis_apply (S : Finset (ι → ℤ)) (x : Finite S) :
    synthesis S x = ∑ k : ↥S, x k • mFourierLp 2 k.val := by
  simp only [synthesis, sum_apply, ContinuousLinearMap.smulRight_apply]
  rfl

/-- Extract the Fourier coordinates belonging to the finite frequency set. -/
def analysis (S : Finset (ι → ℤ)) : Full →L[ℂ] Finite S := (synthesis S).adjoint

private theorem synthesis_single (S : Finset (ι → ℤ)) (k : ↥S) :
    synthesis S (EuclideanSpace.single k (1 : ℂ)) = mFourierLp 2 k.val := by
  classical
  rw [synthesis_apply, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem analysis_apply (S : Finset (ι → ℤ)) (f : Full) (k : ↥S) :
    analysis S f k = mFourierCoeff f k.val := by
  classical
  calc
    _ = inner ℂ (EuclideanSpace.single k (1 : ℂ)) (analysis S f) := by
      rw [EuclideanSpace.inner_single_left, map_one, one_mul]
    _ = inner ℂ (synthesis S (EuclideanSpace.single k (1 : ℂ))) f :=
      (synthesis S).adjoint_inner_right _ _
    _ = _ := by
      rw [synthesis_single, ← mFourierBasis_repr, HilbertBasis.repr_apply_apply, coe_mFourierBasis]

theorem coefficient_synthesis (S : Finset (ι → ℤ)) (x : Finite S) (k : ι → ℤ) :
    mFourierCoeff (synthesis S x) k = if hk : k ∈ S then x ⟨k, hk⟩ else 0 := by
  classical
  rw [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, coe_mFourierBasis, synthesis_apply, inner_sum]
  simp only [inner_smul_right, orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι))]
  by_cases hk : k ∈ S
  · rw [dite_eq_left hk, Finset.sum_eq_single (⟨k, hk⟩ : ↥S)]
    · simp
    · intro l _ hl
      have hne : k ≠ l.val := fun h => hl (Subtype.ext h.symm)
      simp [hne]
    · simp
  · rw [dite_eq_right hk]
    exact Finset.sum_eq_zero fun l _ => by
      have hne : k ≠ l.val := fun h => hk (h.symm ▸ l.property)
      simp [hne]

def project (S : Finset (ι → ℤ)) : Full →L[ℂ] Full := (synthesis S).comp (analysis S)

theorem coefficient_project (S : Finset (ι → ℤ)) (f : Full) (k : ι → ℤ) :
    mFourierCoeff (project S f) k = if k ∈ S then mFourierCoeff f k else 0 := by
  classical
  change mFourierCoeff (synthesis S (analysis S f)) k = _
  rw [coefficient_synthesis]
  split_ifs with hk
  · exact analysis_apply S f ⟨k, hk⟩
  · rfl

/-- Fourier Galerkin projections exhaust the full state in the L² norm,
along the directed family of all finite frequency sets. -/
theorem project_tendsto (f : Full) : Tendsto (fun S : Finset (ι → ℤ) => project S f) atTop (𝓝 f) := by
  have h (S : Finset (ι → ℤ)) : project S f = ∑ k ∈ S, mFourierCoeff f k • mFourierLp 2 k := by
    change synthesis S (analysis S f) = _
    rw [synthesis_apply, ← Finset.sum_coe_sort S]
    simp only [analysis_apply]
  rw [show (fun S => project S f) = (fun S => ∑ k ∈ S, mFourierCoeff f k • mFourierLp 2 k) from funext h]
  exact hasSum_mFourier_series_L2 f

private theorem parseval (f : Full) : ‖f‖ ^ 2 = ∑' k : ι → ℤ, ‖mFourierCoeff f k‖ ^ 2 := by
  rw [SHE.PredictableL2.realLp_norm_sq]
  exact (hasSum_sq_mFourierCoeff f).tsum_eq.symm

theorem synthesis_norm (S : Finset (ι → ℤ)) (x : Finite S) : ‖synthesis S x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [parseval, EuclideanSpace.norm_sq_eq]
  rw [tsum_eq_sum (s := S) (fun k hk => by simp [coefficient_synthesis, hk]), ← Finset.sum_coe_sort S]
  simp only [coefficient_synthesis, dite_eq_left (Subtype.property _)]

theorem analysis_contraction (S : Finset (ι → ℤ)) (f : Full) : ‖analysis S f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, parseval]
  simp only [analysis_apply]
  rw [Finset.sum_coe_sort S (fun k => ‖mFourierCoeff f k‖ ^ 2)]
  exact (hasSum_sq_mFourierCoeff f).summable.sum_le_tsum S (fun k _ => sq_nonneg _)

theorem projection_contraction (S : Finset (ι → ℤ)) (f : Full) : ‖project S f‖ ≤ ‖f‖ := by
  change ‖synthesis S (analysis S f)‖ ≤ _
  rw [synthesis_norm]
  exact analysis_contraction S f

/-- A uniform estimate on the discarded heat modes at nonnegative times. -/
theorem heat_tail_le (S : Finset (ι → ℤ)) {P Λ t : ℝ} (ht : 0 ≤ t)
    (hΛ : ∀ k ∉ S, Λ ≤ HeatTorusFourier.frequencySquared P k) (f : Full) :
    ‖HeatTorusFourier.heat P t f - project S (HeatTorusFourier.heat P t f)‖ ≤
      Real.exp (-t * Λ) * ‖f‖ := by
  let g := HeatTorusFourier.heat P t f
  let R := Real.exp (-t * Λ)
  have hcoeff (k : ι → ℤ) : mFourierCoeff (g - project S g) k =
      mFourierCoeff g k - mFourierCoeff (project S g) k := by
    simp only [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, inner_sub_right]
  change ‖g - project S g‖ ≤ R * ‖f‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, parseval (g - project S g), parseval f, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (hasSum_sq_mFourierCoeff (g - project S g)).summable
    ((hasSum_sq_mFourierCoeff f).summable.mul_left (R ^ 2))
  intro k
  rw [hcoeff, coefficient_project]
  by_cases hk : k ∈ S
  · simp only [ite_eq_left hk, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · rw [ite_eq_right hk, sub_zero, show mFourierCoeff g k = _ from HeatTorusFourier.fourierCoeff_heat P t f k,
      norm_mul, mul_pow]
    have hm : ‖HeatTorusFourier.multiplier P t k‖ ≤ R := by
      rw [HeatTorusFourier.multiplier, max_eq_left ht, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hΛ k hk) (neg_nonpos.mpr ht))
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm 2) (sq_nonneg _)

end HeatTorusGalerkinProjection

#print axioms HeatTorusGalerkinProjection.project_tendsto
#print axioms HeatTorusGalerkinProjection.projection_contraction
#print axioms HeatTorusGalerkinProjection.heat_tail_le
