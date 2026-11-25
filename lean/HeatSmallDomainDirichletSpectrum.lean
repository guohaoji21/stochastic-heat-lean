import HeatSmallDomainDirichletResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace HeatSmallDomainDirichletSpectrum

open Set EllipticPdes EllipticPdes.Sobolev HeatSmallDomainDirichletResolvent
open scoped RealInnerProductSpace

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

abbrev unitStep (Ω : Set (EuclideanSpace ℝ (Fin d))) : L2D Ω →L[ℝ] L2D Ω :=
  step one_pos

/-- A nonzero eigenvector of the unit resolvent is a weak Dirichlet
Laplacian eigenvector. Its energy eigenvalue is `μ⁻¹ - 1`. -/
theorem weak_eigen (ho : IsOpen Ω) {f : L2D Ω} (hf : f ≠ 0) {μ : ℝ}
    (he : unitStep Ω f = μ • f) :
    0 < μ ∧ μ ≤ 1 ∧ ∃ u : H01 Ω,
      embL2 Ω u = f ∧ ∀ v : H01 Ω, laplaceBilin Ω u v = (μ⁻¹ - 1) * ⟪f, embL2 Ω v⟫ := by
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hf
    apply step_injective one_pos ho
    rw [map_zero, he, h, zero_smul]
  have hμ : 0 < μ := by
    have h := inner_self_nonneg one_pos f
    rw [show step one_pos f = μ • f from he, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hf))).mp h)
      hμ₀.symm
  have hμ₁ : μ ≤ 1 := by
    have h := contraction one_pos f
    rw [show step one_pos f = μ • f from he, norm_smul, Real.norm_of_nonneg hμ.le] at h
    exact le_of_mul_le_mul_right (h.trans_eq (one_mul _).symm) (norm_pos_iff.mpr hf)
  let w := solution one_pos f
  have hw : embL2 Ω w = μ • f := (step_apply one_pos f).symm.trans he
  refine ⟨hμ, hμ₁, μ⁻¹ • w, ?_, ?_⟩
  · rw [map_smul, hw, smul_smul, inv_mul_cancel₀ hμ₀, one_smul]
  · intro v
    have hv := variational one_pos f v
    rw [one_mul, he, real_inner_smul_left] at hv
    change μ * ⟪f, embL2 Ω v⟫ + laplaceBilin Ω w v = _ at hv
    have h' : laplaceBilin Ω w v = (1 - μ) * ⟪f, embL2 Ω v⟫ := by linarith only [hv]
    rw [map_smul, smul_apply, smul_eq_mul, h']
    field_simp [hμ₀]

theorem energy_eigenvalue_nonneg {μ : ℝ} (hμ : 0 < μ) (hμ₁ : μ ≤ 1) :
    0 ≤ μ⁻¹ - 1 :=
  sub_nonneg.mpr ((one_le_inv₀ hμ).mpr hμ₁)

/-- Every eigenspace of the unit resolvent diagonalizes all positive
resolvent steps with the same Laplace eigenvalue. -/
theorem step_eigen (ho : IsOpen Ω) {μ a : ℝ} (ha : 0 < a) (f : L2D Ω)
    (he : unitStep Ω f = μ • f) :
    step ha f = (1 + a * (μ⁻¹ - 1))⁻¹ • f := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨hμ, hμ₁, u, hu, hweak⟩ := weak_eigen ho hf he
  let rate := μ⁻¹ - 1
  let c := (1 + a * rate)⁻¹
  have hc : 1 + a * rate ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ha.le (energy_eigenvalue_nonneg hμ hμ₁))).ne'
  have hs : c • u = solution ha f := by
    apply unique_solution ha
    intro v
    rw [map_smul, hu, real_inner_smul_left, map_smul, smul_apply, smul_eq_mul, hweak]
    change c * ⟪f, embL2 Ω v⟫ + a * (c * (rate * ⟪f, embL2 Ω v⟫)) = _
    dsimp only [c]
    field_simp [hc]
    <;> ring
  rw [step_apply, ← hs, map_smul, hu]

/-- The algebraic span of resolvent eigenvectors is dense on bounded domains. -/
theorem dense_eigenspaces (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) :
    Dense ((⨆ μ : ℝ, Module.End.eigenspace (unitStep Ω).toLinearMap μ :
      Submodule ℝ (L2D Ω)) : Set (L2D Ω)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  exact spectral_complete one_pos hm hb

end HeatSmallDomainDirichletSpectrum

#print axioms HeatSmallDomainDirichletSpectrum.weak_eigen
#print axioms HeatSmallDomainDirichletSpectrum.step_eigen
#print axioms HeatSmallDomainDirichletSpectrum.dense_eigenspaces
