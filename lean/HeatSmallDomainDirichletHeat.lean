import HeatSmallDomainDirichletSpectrum
import HeatEulerScalar
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
noncomputable section

namespace HeatSmallDomainDirichletHeat

open Filter MeasureTheory Set EllipticPdes.Sobolev
open HeatSmallDomainDirichletSpectrum
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The normalized resolvent family, with the identity at step size zero. -/
def resolvent (a : ℝ≥0) : L2D Ω →L[ℝ] L2D Ω :=
  if h : 0 < a then HeatSmallDomainDirichletResolvent.step (show 0 < (a : ℝ) by exact_mod_cast h)
  else ContinuousLinearMap.id ℝ (L2D Ω)

theorem resolvent_zero : resolvent (Ω := Ω) 0 = ContinuousLinearMap.id ℝ (L2D Ω) := by
  simp [resolvent]

theorem resolvent_contraction (a : ℝ≥0) (f : L2D Ω) : ‖resolvent a f‖ ≤ ‖f‖ := by
  unfold resolvent
  split
  · exact HeatSmallDomainDirichletResolvent.contraction _ f
  · rfl

theorem resolvent_inner_symm (a : ℝ≥0) (f g : L2D Ω) : ⟪resolvent a f, g⟫ = ⟪f, resolvent a g⟫ := by
  unfold resolvent
  split
  · exact HeatSmallDomainDirichletResolvent.inner_symm _ f g
  · rfl

theorem resolvent_nonnegative (ho : IsOpen Ω) (a : ℝ≥0) (f : L2D Ω)
    (hf : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict Ω, 0 ≤ resolvent a f x := by
  unfold resolvent
  split
  · exact HeatSmallDomainDirichletResolvent.step_nonnegative _ ho f hf
  · exact hf

private theorem resolvent_eigen (ho : IsOpen Ω) (a : ℝ≥0) (f : L2D Ω) {μ : ℝ}
    (he : unitStep Ω f = μ • f) :
    resolvent a f = (1 + (a : ℝ) * (μ⁻¹ - 1))⁻¹ • f := by
  by_cases h : 0 < a
  · rw [resolvent, dif_pos h]
    exact step_eigen ho _ f he
  · have ha : a = 0 := le_antisymm (le_of_not_gt h) a.property
    simp [ha, resolvent_zero]

/-- Operators in the backward Euler scheme. -/
def euler (t : ℝ≥0) (n : ℕ) : L2D Ω →L[ℝ] L2D Ω :=
  (resolvent (t / (n : ℝ≥0))) ^ n

private theorem pow_eigen {a : ℝ≥0} (f : L2D Ω) {c : ℝ} (he : resolvent a f = c • f) (n : ℕ) :
    (resolvent a ^ n) f = c ^ n • f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, he, smul_smul, pow_succ]

private theorem pow_contraction (a : ℝ≥0) (n : ℕ) (f : L2D Ω) :
    ‖(resolvent a ^ n) f‖ ≤ ‖f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact (resolvent_contraction a _).trans ih

private theorem pow_inner_symm (a : ℝ≥0) (n : ℕ) (f g : L2D Ω) :
    ⟪(resolvent a ^ n) f, g⟫ = ⟪f, (resolvent a ^ n) g⟫ := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    nth_rw 1 [pow_succ']
    rw [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      resolvent_inner_symm, ih]

private theorem pow_nonnegative (ho : IsOpen Ω) (a : ℝ≥0) (n : ℕ) (f : L2D Ω)
    (hf : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict Ω, 0 ≤ (resolvent a ^ n) f x := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact resolvent_nonnegative ho a _ ih

private theorem tendsto_eigen (ho : IsOpen Ω) (t : ℝ≥0) (f : L2D Ω) {μ : ℝ}
    (he : unitStep Ω f = μ • f) :
    Tendsto (fun n : ℕ => euler t n f) atTop (𝓝 (Real.exp (-(t : ℝ) * (μ⁻¹ - 1)) • f)) := by
  have h (n : ℕ) : euler t n f = ((1 + (t : ℝ) * (μ⁻¹ - 1) / (n : ℝ))⁻¹)^n • f := by
    rw [euler, pow_eigen f (resolvent_eigen ho _ f he)]
    simp only [NNReal.coe_div, NNReal.coe_natCast, div_mul_eq_mul_div]
  simp_rw [h]
  simpa only [neg_mul] using (HeatEulerScalar.tendsto_inverse ((t : ℝ) * (μ⁻¹ - 1))).smul_const f

private def convergentSubmodule (t : ℝ≥0) : Submodule ℝ (L2D Ω) where
  carrier := {f | ∃ v, Tendsto (fun n : ℕ => euler t n f) atTop (𝓝 v)}
  zero_mem' := ⟨0, by simpa only [map_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : L2D Ω)) atTop (𝓝 0))⟩
  add_mem' := by
    rintro f g ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, by simpa only [map_add] using hy.add hz⟩
  smul_mem' := by
    rintro c f ⟨y, hy⟩
    exact ⟨c • y, by simpa only [map_smul] using hy.const_smul c⟩

private theorem dense_of_eigenspaces (hm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (S : Submodule ℝ (L2D Ω)) (hS : ∀ (μ : ℝ) (f : L2D Ω), unitStep Ω f = μ • f → f ∈ S) :
    Dense (S : Set (L2D Ω)) := by
  apply (dense_eigenspaces hm hb).mono
  change (⨆ μ : ℝ, Module.End.eigenspace (unitStep Ω).toLinearMap μ) ≤ S
  exact iSup_le fun μ f hf => hS μ f (Module.End.mem_eigenspace_iff.mp hf)

private theorem dense_convergent (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0) :
    Dense ((convergentSubmodule (Ω := Ω) t : Submodule ℝ (L2D Ω)) : Set (L2D Ω)) := by
  exact dense_of_eigenspaces ho.measurableSet hb _ fun _ f hf => ⟨_, tendsto_eigen ho t f hf⟩

private theorem cauchy_orbit (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0)
    (f : L2D Ω) : CauchySeq (fun n : ℕ => euler t n f) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (dense_convergent ho hb t f) (ε / 4) (by positivity)
  obtain ⟨y, hy⟩ := hg
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hcon (k : ℕ) : dist (euler t k f) (euler t k g) ≤ dist f g := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact pow_contraction _ _ _
  have h₁ := dist_triangle (euler t m f) (euler t m g) (euler t n f)
  have h₂ := dist_triangle (euler t m g) y (euler t n f)
  have h₃ := dist_triangle y (euler t n g) (euler t n f)
  rw [dist_comm y (euler t n g), dist_comm (euler t n g) (euler t n f)] at h₃
  linarith [hcon m, hcon n, hN m hm, hN n hn]

private def limit (t : ℝ≥0) (f : L2D Ω) : L2D Ω :=
  limUnder atTop (fun n : ℕ => euler t n f)

private theorem tendsto_limit (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0) (f : L2D Ω) :
    Tendsto (fun n : ℕ => euler t n f) atTop (𝓝 (limit t f)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchy_orbit ho hb t f))

/-- The Dirichlet heat flow is the strong limit of backward Euler for the
variational Dirichlet resolvent on a bounded open set. -/
def heat (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0) : L2D Ω →L[ℝ] L2D Ω :=
  (show L2D Ω →ₗ[ℝ] L2D Ω from
    { toFun := limit t
      map_add' := fun f g => tendsto_nhds_unique (tendsto_limit ho hb t (f + g))
        (by simpa only [map_add] using (tendsto_limit ho hb t f).add (tendsto_limit ho hb t g))
      map_smul' := fun c f => tendsto_nhds_unique (tendsto_limit ho hb t (c • f))
        (by simpa only [map_smul, RingHom.id_apply] using (tendsto_limit ho hb t f).const_smul c) }).mkContinuous
    1 (fun f => by
      rw [one_mul]
      exact le_of_tendsto (tendsto_limit ho hb t f).norm (Eventually.of_forall
        fun n => pow_contraction (t / (n : ℝ≥0)) n f))

theorem euler_tendsto_heat (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0) (f : L2D Ω) :
    Tendsto (fun n : ℕ => euler t n f) atTop (𝓝 (heat ho hb t f)) :=
  tendsto_limit ho hb t f

theorem heat_eigen (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0)
    (f : L2D Ω) {μ : ℝ} (he : unitStep Ω f = μ • f) :
    heat ho hb t f = Real.exp (-(t : ℝ) * (μ⁻¹ - 1)) • f :=
  tendsto_nhds_unique (euler_tendsto_heat ho hb t f) (tendsto_eigen ho t f he)

theorem heat_contraction (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0) (f : L2D Ω) :
    ‖heat ho hb t f‖ ≤ ‖f‖ :=
  le_of_tendsto (euler_tendsto_heat ho hb t f).norm (Eventually.of_forall fun n => pow_contraction _ n f)

theorem heat_zero (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    heat ho hb 0 = ContinuousLinearMap.id ℝ (L2D Ω) := by
  ext f : 1
  apply tendsto_nhds_unique (euler_tendsto_heat ho hb 0 f)
  have hz (n : ℕ) : euler 0 n f = f := by
    rw [euler, zero_div, resolvent_zero, ← ContinuousLinearMap.one_def, one_pow]
    rfl
  simp only [hz, ContinuousLinearMap.id_apply]
  exact tendsto_const_nhds

theorem heat_inner_symm (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0)
    (f g : L2D Ω) : ⟪heat ho hb t f, g⟫ = ⟪f, heat ho hb t g⟫ := by
  have h₁ := ((innerSL ℝ g).continuous.continuousAt.tendsto.comp (euler_tendsto_heat ho hb t f))
  have h₂ := ((innerSL ℝ f).continuous.continuousAt.tendsto.comp (euler_tendsto_heat ho hb t g))
  simp only [Function.comp_def, innerSL_apply_apply] at h₁ h₂
  have hs (n : ℕ) : ⟪g, euler t n f⟫ = ⟪f, euler t n g⟫ :=
    (real_inner_comm _ _).trans (pow_inner_symm (t / (n : ℝ≥0)) n f g)
  simp_rw [hs] at h₁
  exact (real_inner_comm _ _).trans (tendsto_nhds_unique h₁ h₂)

theorem heat_nonnegative (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0) (f : L2D Ω)
    (hf : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ f x) :
    ∀ᵐ x ∂volume.restrict Ω, 0 ≤ heat ho hb t f x := by
  obtain ⟨σ, _, hσ⟩ := (tendstoInMeasure_of_tendsto_Lp
    (euler_tendsto_heat ho hb t f)).exists_seq_tendsto_ae
  have hpos (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ euler t n f x :=
    pow_nonnegative ho (t / (n : ℝ≥0)) n f hf
  filter_upwards [hσ, ae_all_iff.mpr hpos] with x hx hn
  exact ge_of_tendsto hx (Eventually.of_forall fun n => hn (σ n))

theorem heat_add (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (s t : ℝ≥0) :
    heat ho hb (s + t) = (heat ho hb s).comp (heat ho hb t) := by
  let A := heat ho hb (s + t)
  let B := (heat ho hb s).comp (heat ho hb t)
  have hD : Dense ((A - B).toLinearMap.ker : Set (L2D Ω)) := by
    apply dense_of_eigenspaces ho.measurableSet hb
    intro μ f hf
    change A f - B f = 0
    apply sub_eq_zero.mpr
    change heat ho hb (s + t) f = heat ho hb s (heat ho hb t f)
    rw [heat_eigen ho hb (s + t) f hf, heat_eigen ho hb t f hf, map_smul,
      heat_eigen ho hb s f hf, smul_smul, ← Real.exp_add, NNReal.coe_add]
    congr 2
    ring
  apply ContinuousLinearMap.ext
  intro f
  exact closure_minimal (fun x hx => sub_eq_zero.mp (show A x - B x = 0 from hx))
    (isClosed_eq A.continuous B.continuous) (hD f)

theorem heat_injective (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (t : ℝ≥0) :
    Function.Injective (heat ho hb t) := by
  apply (injective_iff_map_eq_zero (heat ho hb t)).2
  intro f hf
  have hD : Dense ((innerSL ℝ f).toLinearMap.ker : Set (L2D Ω)) := by
    apply dense_of_eigenspaces ho.measurableSet hb
    intro μ g hg
    change ⟪f, g⟫ = 0
    have h := heat_inner_symm ho hb t f g
    rw [hf, inner_zero_left, heat_eigen ho hb t g hg, real_inner_smul_right] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Real.exp_pos _).ne'
  apply ext_inner_right (𝕜 := ℝ)
  intro g
  have h : ⟪f, g⟫ = 0 :=
    closure_minimal (fun _ hx => hx) (isClosed_eq (innerSL ℝ f).continuous continuous_const) (hD g)
  simpa only [inner_zero_left] using h

/-- Strong continuity follows from continuity of the scalar exponential on
eigenspaces and the uniform contraction bound. -/
theorem heat_continuous (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (f : L2D Ω) :
    Continuous (fun t : ℝ≥0 => heat ho hb t f) := by
  let S : Submodule ℝ (L2D Ω) :=
    { carrier := {f | Continuous (fun t : ℝ≥0 => heat ho hb t f)}
      zero_mem' := by
        change Continuous (fun t : ℝ≥0 => heat ho hb t (0 : L2D Ω))
        simpa only [map_zero] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : L2D Ω)))
      add_mem' := fun {x y} hx hy => by
        change Continuous (fun t : ℝ≥0 => heat ho hb t (x + y))
        rw [show (fun t : ℝ≥0 => heat ho hb t (x + y)) =
          (fun t : ℝ≥0 => heat ho hb t x + heat ho hb t y) from funext (fun t => map_add _ _ _)]
        exact (show Continuous (fun t : ℝ≥0 => heat ho hb t x) from hx).add hy
      smul_mem' := fun c x hx => by
        change Continuous (fun t : ℝ≥0 => heat ho hb t (c • x))
        simp_rw [map_smul]
        exact (show Continuous (fun t : ℝ≥0 => heat ho hb t x) from hx).const_smul c }
  have hD : Dense (S : Set (L2D Ω)) := by
    apply dense_of_eigenspaces ho.measurableSet hb
    intro μ x hx
    change Continuous (fun t : ℝ≥0 => heat ho hb t x)
    simp_rw [fun t => heat_eigen ho hb t x hx]
    exact (Real.continuous_exp.comp (NNReal.continuous_coe.neg.mul continuous_const)).smul continuous_const
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hD f) (ε / 3) (by positivity)
  have hg' : Continuous (fun t : ℝ≥0 => heat ho hb t g) := hg
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hg'.continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun r hr => ?_⟩
  have hc (t : ℝ≥0) : dist (heat ho hb t f) (heat ho hb t g) ≤ dist f g := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact heat_contraction ho hb t _
  have ht₁ := dist_triangle (heat ho hb r f) (heat ho hb r g) (heat ho hb t f)
  have ht₂ := dist_triangle (heat ho hb r g) (heat ho hb t g) (heat ho hb t f)
  rw [dist_comm (heat ho hb t g) (heat ho hb t f)] at ht₂
  exact lt_of_le_of_lt ht₁ (by linarith [hc r, hc t, hδ' hr])

end HeatSmallDomainDirichletHeat

#print axioms HeatSmallDomainDirichletHeat.euler_tendsto_heat
#print axioms HeatSmallDomainDirichletHeat.heat_eigen
#print axioms HeatSmallDomainDirichletHeat.heat_zero
#print axioms HeatSmallDomainDirichletHeat.heat_inner_symm
#print axioms HeatSmallDomainDirichletHeat.heat_nonnegative
#print axioms HeatSmallDomainDirichletHeat.heat_add
#print axioms HeatSmallDomainDirichletHeat.heat_injective
#print axioms HeatSmallDomainDirichletHeat.heat_continuous
