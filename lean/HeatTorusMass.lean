import HeatTorusSubeigen
import HeatTorusCovarianceSeparation
import HeatRestrictionAdjoint

set_option autoImplicit false
set_option maxHeartbeats 2300000
noncomputable section

namespace HeatTorusMass

open MeasureTheory Set UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation
open scoped NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι]

def Positive (A : RealState ι →L[ℝ] RealState ι) : Prop :=
  ∀ f, (∀ᵐ x ∂volume, 0 ≤ f x) → ∀ᵐ x ∂volume, 0 ≤ A f x

private theorem apply_mono (A : RealState ι →L[ℝ] RealState ι) (hA : Positive A)
    (f g : RealState ι) (hfg : ∀ᵐ x ∂volume, f x ≤ g x) :
    ∀ᵐ x ∂volume, A f x ≤ A g x := by
  have hp : ∀ᵐ x ∂volume, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx he
    rw [he]
    exact sub_nonneg.mpr hx
  have hp' := hA (g - f) hp
  rw [map_sub] at hp'
  filter_upwards [hp', Lp.coeFn_sub (A g) (A f)] with x hx he
  rw [he] at hx
  exact sub_nonneg.mp hx

private theorem scale_le (a b : ℝ) (ha : 0 ≤ a) {f g h : RealState ι}
    (h₁ : ∀ᵐ x ∂volume, (b • f) x ≤ g x)
    (h₂ : ∀ᵐ x ∂volume, (a • g) x ≤ h x) :
    ∀ᵐ x ∂volume, ((a * b) • f) x ≤ h x := by
  filter_upwards [h₁, h₂, Lp.coeFn_smul b f, Lp.coeFn_smul a g, Lp.coeFn_smul (a * b) f]
    with x h₁x h₂x hb hg hf
  rw [hb] at h₁x
  rw [hg] at h₂x
  rw [hf]
  change b * f x ≤ g x at h₁x
  change a * g x ≤ h x at h₂x
  change (a * b) * f x ≤ h x
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left h₁x ha).trans h₂x

private theorem K_ge_of_integrand_ge (P : ℝ) (M : RealState ι →L[ℝ] RealState ι)
    (r : ℝ≥0) (f c : RealState ι)
    (h : ∀ v ∈ Icc (0 : ℝ) 1, ∀ᵐ x ∂volume,
      c x ≤ HeatCovarianceOperator.integrand (family P) M r f v x) :
    ∀ᵐ x ∂volume, c x ≤ K P M r f x := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Ioc]⟩
  let F := HeatCovarianceOperator.integrand (family P) M r f
  have hI : Integrable F ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (HeatCovarianceOperator.integrable (family P) (family_continuous P) (family_contraction P) M r f)
  have hp : ∀ᵐ v ∂ν, ∀ᵐ x ∂volume, 0 ≤ (F v - c) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    filter_upwards [h v ⟨hv.1.le, hv.2⟩, Lp.coeFn_sub (F v) c] with x hx he
    rw [he]
    exact sub_nonneg.mpr hx
  have hi := HeatTorusGaussian.integral_nonnegative ν (fun v => F v - c)
    (hI.sub (integrable_const c)) hp
  rw [integral_sub hI (integrable_const c), integral_const, probReal_univ, one_smul] at hi
  have he : (∫ v, F v ∂ν) = K P M r f := by
    change (∫ v, F v ∂ν) = ∫ v in (0 : ℝ)..1, F v
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [he] at hi
  filter_upwards [hi, Lp.coeFn_sub (K P M r f) c] with x hx hs
  rw [hs] at hx
  exact sub_nonneg.mp hx

theorem K_positive (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) (hM : Positive M) (r : ℝ≥0) :
    Positive (K P M r) := by
  intro f hf
  have hp := K_ge_of_integrand_ge P M r f 0 (fun v _ => by
    have h := HeatTorusGaussian.realHeat_nonnegative P ((((1 - v) * (r : ℝ)).toNNReal : ℝ))
      (M (realHeat P (((v * (r : ℝ)).toNNReal : ℝ)) f))
      (hM _ (HeatTorusGaussian.realHeat_nonnegative P (((v * (r : ℝ)).toNNReal : ℝ)) f hf))
    filter_upwards [h, Lp.coeFn_zero (E := ℝ) (p := 2)
      (μ := (volume : Measure (UnitAddTorus ι)))] with x hx hz
    rw [hz]
    exact hx)
  filter_upwards [hp, Lp.coeFn_zero (E := ℝ) (p := 2)
    (μ := (volume : Measure (UnitAddTorus ι)))] with x hx hz
  rwa [hz] at hx

private theorem inner_mono (q f g : RealState ι) (hq : ∀ᵐ x ∂volume, 0 ≤ q x)
    (hfg : ∀ᵐ x ∂volume, f x ≤ g x) : inner ℝ q f ≤ inner ℝ q g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner q f) (L2.integrable_inner q g)
  filter_upwards [hq, hfg] with x hx hy
  simp only [Real.inner_apply]
  exact mul_le_mul_of_nonneg_left hy hx

section DomainComparison

local notation "Haar[" j "]" => (volume : Measure (UnitAddTorus j))
local notation "R[" D "]" => HeatRestrictionAdjoint.restriction volume D
local notation "E[" D "]" => HeatRestrictionAdjoint.adjointExtension volume D

variable {D : Set (UnitAddTorus ι)} (hD : MeasurableSet D)
local notation "Small[" D "]" => Lp ℝ 2 (Measure.restrict volume D)

include hD in
private theorem restrict_extension (f : Small[D]) : R[D] (E[D] f) = f := by
  apply Lp.ext
  filter_upwards [HeatRestrictionAdjoint.restriction_ae Haar[ι] D (E[D] f),
    ae_restrict_of_ae (HeatRestrictionAdjoint.adjointExtension_ae Haar[ι] D hD f),
    ae_restrict_mem hD] with x hr he hx
  rw [hr, he, indicator_of_mem hx]

include hD in
private theorem extension_restriction (f : RealState ι)
    (hf : ∀ᵐ x ∂Haar[ι], x ∉ D → f x = 0) : E[D] (R[D] f) = f := by
  apply Lp.ext
  filter_upwards [HeatRestrictionAdjoint.adjointExtension_ae Haar[ι] D hD (R[D] f),
    (ae_restrict_iff' hD).mp (HeatRestrictionAdjoint.restriction_ae Haar[ι] D f), hf]
    with x he hr hx
  by_cases hmem : x ∈ D
  · rw [he, indicator_of_mem hmem, hr hmem]
  · rw [he, indicator_of_notMem hmem, hx hmem]

include hD in
private theorem extension_nonnegative (f : Small[D])
    (hf : ∀ᵐ x ∂Measure.restrict Haar[ι] D, 0 ≤ f x) : ∀ᵐ x ∂Haar[ι], 0 ≤ E[D] f x := by
  filter_upwards [HeatRestrictionAdjoint.adjointExtension_ae Haar[ι] D hD f,
    (ae_restrict_iff' hD).mp hf] with x he hf
  rw [he]
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx]
    exact hf hx
  · rw [indicator_of_notMem hx]

variable (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) (hM : Positive M)
  (hfixed : ∀ f : Small[D], M (E[D] f) = E[D] f)
  (S : ℝ≥0 → Small[D] →L[ℝ] Small[D])
  (hSpos : ∀ t (f : Small[D]), (∀ᵐ x ∂Measure.restrict Haar[ι] D, 0 ≤ f x) →
    ∀ᵐ x ∂Measure.restrict Haar[ι] D, 0 ≤ S t f x)
  (hSadd : ∀ a b (f : Small[D]), S (a + b) f = S a (S b f))
  (hdom : ∀ t (f : RealState ι), (∀ᵐ x ∂Haar[ι], 0 ≤ f x) →
    ∀ᵐ x ∂Haar[ι], E[D] (S t (R[D] f)) x ≤ family P t f x)

include hD hM hfixed hSpos hSadd hdom in
/-- Heat domination passes through both heat factors of the covariance step
when multiplication fixes every zero extension from the smaller domain. -/
theorem covariance_domain_comparison (r : ℝ≥0) (f : RealState ι) (hf : ∀ᵐ x ∂Haar[ι], 0 ≤ f x) :
    ∀ᵐ x ∂Haar[ι], E[D] (S r (R[D] f)) x ≤ K P M r f x := by
  apply K_ge_of_integrand_ge
  intro θ hθ
  let a := Real.toNNReal ((1 - θ) * (r : ℝ))
  let b := Real.toNNReal (θ * (r : ℝ))
  have hab : a + b = r := calc
    _ = Real.toNNReal ((1 - θ) * (r : ℝ) + θ * (r : ℝ)) :=
      (Real.toNNReal_add (mul_nonneg (sub_nonneg.mpr hθ.2) r.property)
        (mul_nonneg hθ.1 r.property)).symm
    _ = r := by rw [show (1 - θ) * (r : ℝ) + θ * (r : ℝ) = r by ring, Real.toNNReal_coe]
  have hRf : ∀ᵐ x ∂Measure.restrict Haar[ι] D, 0 ≤ R[D] f x := by
    filter_upwards [HeatRestrictionAdjoint.restriction_ae Haar[ι] D f, ae_restrict_of_ae hf]
      with x hr hx
    rw [hr]
    exact hx
  let v := E[D] (S b (R[D] f))
  have hv : ∀ᵐ x ∂Haar[ι], 0 ≤ v x := extension_nonnegative hD _ (hSpos b _ hRf)
  have hmul := apply_mono M hM v (family P b f) (hdom b f hf)
  change (∀ᵐ x ∂Haar[ι], M (E[D] (S b (R[D] f))) x ≤ M (family P b f) x) at hmul
  rw [hfixed] at hmul
  have hheat := apply_mono (family P a) (HeatTorusGaussian.realHeat_nonnegative P a)
    v (M (family P b f)) hmul
  have hvheat := hdom a v hv
  change (∀ᵐ x ∂Haar[ι], E[D] (S a (R[D] (E[D] (S b (R[D] f))))) x ≤ family P a v x) at hvheat
  rw [restrict_extension hD, ← hSadd, hab] at hvheat
  filter_upwards [hvheat, hheat] with x hx hy using hx.trans hy

include hD hM hfixed hSpos hSadd hdom in
/-- The covariance chain dominates the smaller heat orbit for the sum of
the actual cell lengths. -/
theorem chain_domain_comparison (hSzero : ∀ f, S 0 f = f) (h : ℕ → ℝ≥0) (N : ℕ)
    (g : RealState ι) (hg : ∀ᵐ x ∂Haar[ι], 0 ≤ g x)
    (hsupp : ∀ᵐ x ∂Haar[ι], x ∉ D → g x = 0) (n : ℕ) :
    ∀ᵐ x ∂Haar[ι], E[D] (S (∑ k ∈ Finset.range n, h (N - k)) (R[D] g)) x ≤
      HeatBackwardChain.reverseChain (K P M) h N g n x := by
  have hgR : ∀ᵐ x ∂Measure.restrict Haar[ι] D, 0 ≤ R[D] g x := by
    filter_upwards [HeatRestrictionAdjoint.restriction_ae Haar[ι] D g, ae_restrict_of_ae hg]
      with x hr hx
    rwa [hr]
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, hSzero, extension_restriction hD g hsupp,
      HeatBackwardChain.reverseChain]
    exact Filter.Eventually.of_forall fun _ => le_rfl
  | succ n ih =>
    let a := ∑ k ∈ Finset.range n, h (N - k)
    let r := h (N - n)
    let v := E[D] (S a (R[D] g))
    have hv := extension_nonnegative hD _ (hSpos a _ hgR)
    have hm := apply_mono (K P M r) (K_positive P M hM r) v _ ih
    have hs := covariance_domain_comparison hD P M hM hfixed S hSpos hSadd hdom r v hv
    change (∀ᵐ x ∂Haar[ι], E[D] (S r (R[D] (E[D] (S a (R[D] g))))) x ≤ K P M r v x) at hs
    rw [restrict_extension hD, ← hSadd, add_comm r a] at hs
    rw [Finset.sum_range_succ, HeatBackwardChain.reverseChain]
    filter_upwards [hs, hm] with x hx hy using hx.trans hy

include hD hM hfixed hSpos hSadd hdom in
/-- A positive injective self-adjoint smaller heat flow yields the exact
midpoint norm in the initial pairing. -/
theorem initial_pairing_domain_comparison (hSzero : ∀ f, S 0 f = f)
    (hSsym : ∀ t (x y : Small[D]), inner ℝ (S t x) y = inner ℝ x (S t y))
    (h : ℕ → ℝ≥0) (N : ℕ) (T : ℝ≥0) (hT : ∑ k ∈ Finset.range N, h (N - k) = T)
    (hSinj : Function.Injective (S (T / 2)))
    (g : RealState ι) (hg : ∀ᵐ x ∂Haar[ι], 0 ≤ g x) (hg₀ : g ≠ 0)
    (hsupp : ∀ᵐ x ∂Haar[ι], x ∉ D → g x = 0) :
    0 < ‖S (T / 2) (R[D] g)‖ ^ 2 ∧
      ‖S (T / 2) (R[D] g)‖ ^ 2 ≤ inner ℝ g (HeatBackwardChain.stateAt (K P M) h N g 0) := by
  have hgR : R[D] g ≠ 0 := by
    intro he
    apply hg₀
    rw [← extension_restriction hD g hsupp, he, map_zero]
  have hnonzero : S (T / 2) (R[D] g) ≠ 0 := by
    intro he
    apply hgR
    apply hSinj
    rwa [map_zero]
  refine ⟨sq_pos_of_pos (norm_pos_iff.mpr hnonzero), ?_⟩
  have hcomp := chain_domain_comparison hD P M hM hfixed S hSpos hSadd hdom hSzero h N g hg hsupp N
  rw [hT] at hcomp
  have hpair := inner_mono g _ _ hg hcomp
  rw [← HeatRestrictionAdjoint.restriction_adjoint_pairing] at hpair
  have hmid : T / 2 + T / 2 = T := by ring
  have heq : inner ℝ (R[D] g) (S T (R[D] g)) = ‖S (T / 2) (R[D] g)‖ ^ 2 := by
    calc
      _ = inner ℝ (R[D] g) (S (T / 2) (S (T / 2) (R[D] g))) := by rw [← hSadd, hmid]
      _ = _ := by rw [← hSsym, real_inner_self_eq_norm_sq]
  rw [heq] at hpair
  simpa only [HeatBackwardChain.stateAt, Nat.sub_zero] using hpair

end DomainComparison

/-- A positive multiplier that fixes the barrier preserves its lower bound
through a covariance step, for every step size. -/
theorem K_lower (P C : ℝ) (M : RealState ι →L[ℝ] RealState ι)
    (hM : Positive M) (f g : RealState ι) (hfix : M f = f)
    (hg : HasDerivWithinAt (fun s : ℝ => realHeat P s f) g (Ici 0) 0)
    (hsub : ∀ᵐ x ∂volume, 0 ≤ (g + C • f) x) (r : ℝ≥0) :
    ∀ᵐ x ∂volume, (Real.exp (-C * (r : ℝ)) • f) x ≤ K P M r f x := by
  apply K_ge_of_integrand_ge
  intro v hv
  let s := v * (r : ℝ)
  let t := (1 - v) * (r : ℝ)
  have hs : 0 ≤ s := mul_nonneg hv.1 r.property
  have ht : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hv.2) r.property
  have h₁ := apply_mono M hM _ _ (HeatTorusSubeigen.heat_lower P C f g hg hsub s hs)
  rw [map_smul, hfix] at h₁
  have h₂ := apply_mono (realHeat P t) (HeatTorusGaussian.realHeat_nonnegative P t) _ _ h₁
  rw [map_smul] at h₂
  have h := scale_le (Real.exp (-C * s)) (Real.exp (-C * t)) (Real.exp_pos _).le
    (HeatTorusSubeigen.heat_lower P C f g hg hsub t ht) h₂
  have he : Real.exp (-C * s) * Real.exp (-C * t) = Real.exp (-C * (r : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [s, t]
    ring
  rw [he] at h
  unfold HeatCovarianceOperator.integrand HeatIntervalCovariance.extend
  change ∀ᵐ x ∂volume, (Real.exp (-C * (r : ℝ)) • f) x ≤
    realHeat P (t.toNNReal : ℝ) (M (realHeat P (s.toNNReal : ℝ) f)) x
  rwa [Real.coe_toNNReal _ ht, Real.coe_toNNReal _ hs]

/-- The same barrier works on an arbitrary sequence of covariance steps. -/
theorem reverse_lower (P C : ℝ) (M : RealState ι →L[ℝ] RealState ι)
    (hM : Positive M) (f g : RealState ι) (hfix : M f = f)
    (hg : HasDerivWithinAt (fun s : ℝ => realHeat P s f) g (Ici 0) 0)
    (hsub : ∀ᵐ x ∂volume, 0 ≤ (g + C • f) x)
    (h : ℕ → ℝ≥0) (N : ℕ) (u : RealState ι)
    (hu : ∀ᵐ x ∂volume, f x ≤ u x) (n : ℕ) :
    ∀ᵐ x ∂volume, (Real.exp (-C * ∑ k ∈ Finset.range n, (h (N - k) : ℝ)) • f) x ≤
      HeatBackwardChain.reverseChain (K P M) h N u n x := by
  induction n with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero, one_smul,
      HeatBackwardChain.reverseChain] using hu
  | succ n ih =>
    let r := h (N - n)
    let a := Real.exp (-C * ∑ k ∈ Finset.range n, (h (N - k) : ℝ))
    have h₁ := K_lower P C M hM f g hfix hg hsub r
    have h₂ := apply_mono (K P M r) (K_positive P M hM r) _ _ ih
    rw [map_smul] at h₂
    have he : Real.exp (-C * ∑ k ∈ Finset.range (n + 1), (h (N - k) : ℝ)) =
        a * Real.exp (-C * (r : ℝ)) := by
      rw [Finset.sum_range_succ, ← Real.exp_add]
      congr 1
      dsimp [a, r]
      ring
    rw [he, HeatBackwardChain.reverseChain]
    exact scale_le _ _ (Real.exp_pos _).le h₁ h₂

private theorem reverse_mesh_sum (t : ℕ → ℝ≥0) (ht : Monotone t) (N n : ℕ) (hn : n ≤ N) :
    ∑ k ∈ Finset.range n, ((t (N - k) - t (N - k - 1) : ℝ≥0) : ℝ) =
      (t N : ℝ) - t (N - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hn), NNReal.coe_sub (ht (Nat.sub_le _ _)),
      show N - (n + 1) = N - n - 1 by omega]
    ring

/-- A single nonzero barrier yields a lower bound on the initial pairing
that is independent of the time grid. -/
theorem pairing_lower (P C : ℝ) (M : RealState ι →L[ℝ] RealState ι)
    (hM : Positive M) (f g u : RealState ι) (hfix : M f = f)
    (hg : HasDerivWithinAt (fun s : ℝ => realHeat P s f) g (Ici 0) 0)
    (hsub : ∀ᵐ x ∂volume, 0 ≤ (g + C • f) x)
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x) (hu : ∀ᵐ x ∂volume, f x ≤ u x)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht₀ : t 0 = 0) (N : ℕ) :
    Real.exp (-C * (t N : ℝ)) * ‖f‖ ^ 2 ≤
      inner ℝ u (HeatBackwardChain.stateAt (K P M) (fun j => t j - t (j - 1)) N u 0) := by
  have hu₀ : ∀ᵐ x ∂volume, 0 ≤ u x := by
    filter_upwards [hf, hu] with x hx hy
    exact hx.trans hy
  have h := reverse_lower P C M hM f g hfix hg hsub (fun j => t j - t (j - 1)) N u hu N
  rw [reverse_mesh_sum t ht N N le_rfl, Nat.sub_self, ht₀, NNReal.coe_zero, sub_zero] at h
  have h₁ := inner_mono u _ _ hu₀ h
  rw [real_inner_smul_right] at h₁
  have h₂ := inner_mono f f u hf hu
  rw [real_inner_self_eq_norm_sq, real_inner_comm u f] at h₂
  exact (mul_le_mul_of_nonneg_left h₂ (Real.exp_pos _).le).trans h₁

end HeatTorusMass

#print axioms HeatTorusMass.K_positive
#print axioms HeatTorusMass.covariance_domain_comparison
#print axioms HeatTorusMass.initial_pairing_domain_comparison
#print axioms HeatTorusMass.K_lower
#print axioms HeatTorusMass.reverse_lower
#print axioms HeatTorusMass.pairing_lower
