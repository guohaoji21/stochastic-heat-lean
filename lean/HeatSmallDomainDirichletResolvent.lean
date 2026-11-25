import EllipticPdes.Analysis.WeakConvergence
import EllipticPdes.Sobolev.GraphDense
import EllipticPdes.Sobolev.H01Lattice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 150000
noncomputable section

namespace HeatSmallDomainDirichletResolvent

open MeasureTheory Filter Set EllipticPdes EllipticPdes.Sobolev
open scoped RealInnerProductSpace

variable {d : ℕ}
variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

private def massForm (Ω : Set (EuclideanSpace ℝ (Fin d))) : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (embL2 Ω) (embL2 Ω)

/-- The form of the resolvent of the Dirichlet Laplacian. -/
def form (Ω : Set (EuclideanSpace ℝ (Fin d))) (a : ℝ) : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ :=
  massForm Ω + a • laplaceBilin Ω

theorem form_apply (a : ℝ) (u v : H01 Ω) :
    form Ω a u v = ⟪embL2 Ω u, embL2 Ω v⟫ + a * laplaceBilin Ω u v := by
  simp only [form, massForm, add_apply, smul_apply, ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply, smul_eq_mul]

theorem form_symm (a : ℝ) (u v : H01 Ω) : form Ω a u v = form Ω a v u := by
  rw [form_apply, form_apply, real_inner_comm (embL2 Ω v), laplaceBilin_symm Ω v u]

theorem form_coercive {a : ℝ} (ha : 0 < a) : IsCoercive (form Ω a) := by
  refine ⟨min 1 a, lt_min one_pos ha, fun u => ?_⟩
  have h := H01.norm_sq_eq u
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) a) (sq_nonneg ‖embL2 Ω u‖)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) a)
    (Finset.sum_nonneg (s := (Finset.univ : Finset (Fin d))) (fun i _ => sq_nonneg ‖H01.grad u i‖))
  change ‖u‖ ^ 2 = ‖embL2 Ω u‖ ^ 2 + ∑ i : Fin d, ‖(u : H1amb Ω) i.succ‖ ^ 2 at h
  rw [form_apply, real_inner_self_eq_norm_sq, laplaceBilin_self, mul_assoc, ← pow_two,
    h, mul_add]
  exact add_le_add (h₁.trans_eq (one_mul _)) h₂

def solution {a : ℝ} (ha : 0 < a) : L2D Ω →L[ℝ] H01 Ω :=
  ((form_coercive (Ω := Ω) ha).continuousLinearEquivOfBilin.symm : H01 Ω →L[ℝ] H01 Ω).comp
    (embL2 Ω).adjoint

/-- The (L²) realization of the variational Dirichlet resolvent. -/
def step {a : ℝ} (ha : 0 < a) : L2D Ω →L[ℝ] L2D Ω :=
  solOp (form Ω a) (form_coercive ha)

theorem step_apply {a : ℝ} (ha : 0 < a) (f : L2D Ω) :
    step ha f = embL2 Ω (solution ha f) := rfl

theorem variational {a : ℝ} (ha : 0 < a) (f : L2D Ω) (v : H01 Ω) :
    ⟪step ha f, embL2 Ω v⟫ + a * laplaceBilin Ω (solution ha f) v = ⟪f, embL2 Ω v⟫ := by
  rw [step_apply, ← form_apply, ← (form_coercive ha).continuousLinearEquivOfBilin_apply]
  unfold solution
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem unique_solution {a : ℝ} (ha : 0 < a) (f : L2D Ω) (u : H01 Ω)
    (hu : ∀ v : H01 Ω, ⟪embL2 Ω u, embL2 Ω v⟫ + a * laplaceBilin Ω u v = ⟪f, embL2 Ω v⟫) :
    u = solution ha f := by
  apply (form_coercive (Ω := Ω) ha).continuousLinearEquivOfBilin.injective
  apply ext_inner_right (𝕜 := ℝ)
  intro v
  rw [(form_coercive ha).continuousLinearEquivOfBilin_apply,
    (form_coercive ha).continuousLinearEquivOfBilin_apply, form_apply, form_apply,
    hu v, ← step_apply, variational]

theorem inner_symm {a : ℝ} (ha : 0 < a) (f g : L2D Ω) : ⟪step ha f, g⟫ = ⟪f, step ha g⟫ :=
  solOp_inner_symm (form_coercive ha) (form_symm a) f g

theorem inner_self_nonneg {a : ℝ} (ha : 0 < a) (f : L2D Ω) : 0 ≤ ⟪step ha f, f⟫ :=
  solOp_inner_self_nonneg (form_coercive ha) f

theorem contraction {a : ℝ} (ha : 0 < a) (f : L2D Ω) : ‖step ha f‖ ≤ ‖f‖ := by
  by_cases h : step ha f = 0
  · simp [h]
  have hp := norm_pos_iff.mpr h
  have hv := variational ha f (solution ha f)
  rw [← step_apply, real_inner_self_eq_norm_sq] at hv
  have hn : 0 ≤ laplaceBilin Ω (solution ha f) (solution ha f) := by
    rw [laplaceBilin_self]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hle := (real_inner_le_norm f (step ha f))
  apply le_of_mul_le_mul_right _ hp
  rw [← pow_two]
  linarith [mul_nonneg ha.le hn]

/-- Nonnegative data give a nonnegative resolvent solution, by testing
the variational equation with the negative part. -/
theorem step_nonnegative {a : ℝ} (ha : 0 < a) (ho : IsOpen Ω) (f : L2D Ω)
    (hf : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict Ω, 0 ≤ step ha f x := by
  let u := solution ha f
  obtain ⟨w, hw, hw₀, hwgrad⟩ :=
    exists_mem_H01_posPart_sub_const ho (-u).2 (k := 0) le_rfl
  let v : H01 Ω := ⟨w, hw⟩
  have hv₀ : ∀ᵐ x ∂volume.restrict Ω, embL2 Ω v x = max (-embL2 Ω u x) 0 := by
    filter_upwards [hw₀, Lp.coeFn_neg ((u : H1amb Ω) 0)] with x h₀ hneg
    change w 0 x = max (-((u : H1amb Ω) 0 x)) 0
    simpa only [Submodule.coe_neg, PiLp.neg_apply, sub_zero, hneg, Pi.neg_apply] using h₀
  have hgrad (i : Fin d) :
      ∀ᵐ x ∂volume.restrict Ω, H01.grad v i x =
        if 0 < -embL2 Ω u x then -H01.grad u i x else 0 := by
    filter_upwards [hwgrad i, Lp.coeFn_neg ((u : H1amb Ω) 0),
      Lp.coeFn_neg ((u : H1amb Ω) i.succ)] with x h₀ hneg hneg'
    change w i.succ x = _
    simpa only [Submodule.coe_neg, PiLp.neg_apply, hneg, hneg', Pi.neg_apply, H01.grad_def,
      embL2_apply] using h₀
  have hmass : ⟪embL2 Ω u, embL2 Ω v⟫ = -‖embL2 Ω v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.real_inner_eq_integral, L2.real_inner_eq_integral,
      ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hv₀] with x hx
    rw [hx]
    by_cases h : 0 ≤ -embL2 Ω u x
    · rw [max_eq_left h]; ring
    · rw [max_eq_right (le_of_not_ge h)]
      ring
  have henergy : laplaceBilin Ω u v = -(∑ i, ‖H01.grad v i‖^2) := by
    rw [laplaceBilin_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change ⟪H01.grad u i, H01.grad v i⟫ = -‖H01.grad v i‖ ^ 2
    rw [← real_inner_self_eq_norm_sq, L2.real_inner_eq_integral, L2.real_inner_eq_integral,
      ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hgrad i] with x hx
    rw [hx]
    split_ifs <;> ring
  have hright : 0 ≤ ⟪f, embL2 Ω v⟫ := by
    rw [L2.real_inner_eq_integral]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hv₀] with x hfx hvx
    rw [hvx]
    exact mul_nonneg hfx (le_max_right _ _)
  have he := variational ha f v
  rw [step_apply] at he
  change ⟪embL2 Ω u, embL2 Ω v⟫ + a * laplaceBilin Ω u v = _ at he
  rw [hmass, henergy] at he
  have hvzero : embL2 Ω v = 0 := by
    apply norm_eq_zero.mp
    have hs : 0 ≤ a * ∑ i, ‖H01.grad v i‖ ^ 2 :=
      mul_nonneg ha.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    nlinarith only [he, hs, hright, sq_nonneg ‖embL2 Ω v‖, norm_nonneg (embL2 Ω v)]
  have hvzero' := (Lp.eq_zero_iff_ae_eq_zero.mp hvzero)
  filter_upwards [hvzero', hv₀] with x hzero hx
  rw [step_apply]
  change 0 ≤ embL2 Ω u x
  have h := le_max_left (-embL2 Ω u x) (0 : ℝ)
  rw [← hx, hzero] at h
  exact neg_nonpos.mp (show -embL2 Ω u x ≤ (0 : ℝ) from h)

theorem spectral_complete {a : ℝ} (ha : 0 < a)
    (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) :
    (⨆ μ : ℝ, Module.End.eigenspace (step (Ω := Ω) ha).toLinearMap μ)ᗮ = ⊥ :=
  solOp_spectral (form_coercive ha) (form_symm a) (embL2_isCompact hm hb)

theorem denseRange_embedding (ho : IsOpen Ω) : DenseRange (embL2 Ω) := by
  have h := H1Graph.denseRange_embL2 (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) ho
  change Dense (range (H1Graph.embL2 volume Ω)) at h
  change Dense (range (embL2 Ω))
  apply h.mono
  rintro _ ⟨u, rfl⟩
  refine ⟨(H1Graph.h01Equiv Ω).symm u, ?_⟩
  rw [embL2_apply]
  rw [← H1Graph.embL2_h01Equiv, LinearIsometryEquiv.apply_symm_apply]

theorem step_injective {a : ℝ} (ha : 0 < a) (ho : IsOpen Ω) :
    Function.Injective (step (Ω := Ω) ha) := by
  apply (injective_iff_map_eq_zero (step (Ω := Ω) ha)).2
  intro f hf
  have hz : solution ha f = 0 := by
    apply embL2_injective ho
    rw [← step_apply, hf, map_zero]
  apply ext_inner_right (𝕜 := ℝ)
  intro g
  have hclosed : IsClosed {z : L2D Ω | ⟪f, z⟫ = 0} :=
    isClosed_eq (innerSL ℝ f).continuous continuous_const
  have hm : range (embL2 Ω) ⊆ {z : L2D Ω | ⟪f, z⟫ = 0} := by
    rintro z ⟨u, rfl⟩
    have h := variational ha f u
    have ha' : laplaceBilin Ω (solution ha f) u = 0 := by
      rw [hz]
      simp
    rw [hf, ha', inner_zero_left, mul_zero, add_zero] at h
    exact h.symm
  have hc : g ∈ closure (range (embL2 Ω)) := (denseRange_embedding ho) g
  simpa using closure_minimal hm hclosed hc

end HeatSmallDomainDirichletResolvent

#print axioms HeatSmallDomainDirichletResolvent.variational
#print axioms HeatSmallDomainDirichletResolvent.unique_solution
#print axioms HeatSmallDomainDirichletResolvent.inner_symm
#print axioms HeatSmallDomainDirichletResolvent.inner_self_nonneg
#print axioms HeatSmallDomainDirichletResolvent.contraction
#print axioms HeatSmallDomainDirichletResolvent.step_nonnegative
#print axioms HeatSmallDomainDirichletResolvent.spectral_complete
#print axioms HeatSmallDomainDirichletResolvent.step_injective
