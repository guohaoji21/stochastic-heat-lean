import HeatDirichletEuler
import HeatPositiveCone
import HeatResolventApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatSubeigenEuler
open MeasureTheory Filter HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolvent
open HeatEulerScalar
open scoped Topology

theorem smul_nonnegative (c : ℝ) (hc : 0 ≤ c) (f : Base) (hf : ∀ᵐ x ∂baseMeasure,0 ≤ f x) :
    ∀ᵐ x ∂baseMeasure,0 ≤ (c • f) x := by
  filter_upwards [hf,Lp.coeFn_smul c f] with x hx hs
  rw [hs]
  exact mul_nonneg hc hx

theorem add_nonnegative (f g : Base) (hf : ∀ᵐ x ∂baseMeasure,0 ≤ f x)
    (hg : ∀ᵐ x ∂baseMeasure,0 ≤ g x) : ∀ᵐ x ∂baseMeasure,0 ≤ (f+g) x := by
  filter_upwards [hf,hg,Lp.coeFn_add f g] with x hx hy hs
  rw [hs]
  exact add_nonneg hx hy

theorem resolvent_barrier {a C : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C) (f g : Base)
    (hfg : weakLaplacian f g) (hpos : ∀ᵐ x ∂baseMeasure,0 ≤ (g+C • f) x) :
    ∀ᵐ x ∂baseMeasure,0 ≤ (smoothing a ha f-(a/(a+C)) • f) x := by
  let w := g+C • f
  have hw : resolvent a ha w=(a+C) • resolvent a ha f-f := by
    calc
      _ = resolvent a ha ((a+C) • f-(a • f-g)) := congrArg (resolvent a ha) (by dsimp [w];module)
      _ = _ := by rw [map_sub,map_smul,HeatResolventApproximation.inverts ha f g hfg]
  have hd : a+C≠0 := ne_of_gt (by linarith)
  have hm : 0 ≤ a/(a+C) := div_nonneg (by linarith) (by linarith)
  have he : smoothing a ha f-(a/(a+C)) • f=(a/(a+C)) • resolvent a ha w := by
    rw [hw,smul_sub,smul_smul,div_mul_cancel₀ _ hd]
    rfl
  rw [he]
  exact smul_nonnegative _ hm _ (HeatResolventPositivity.nonnegative ha w hpos)

theorem iterate_barrier {a C : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C) (f g : Base)
    (hfg : weakLaplacian f g) (hpos : ∀ᵐ x ∂baseMeasure,0 ≤ (g+C • f) x) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure,0 ≤ (((smoothing a ha : Base → Base)^[n]) f-(a/(a+C))^n • f) x := by
  have hm : 0 ≤ a/(a+C) := div_nonneg (by linarith) (by linarith)
  induction n with
  | zero =>
    simp only [Function.iterate_zero,Function.id_def,pow_zero,one_smul,sub_self]
    exact Lp.coeFn_zero ℝ 2 baseMeasure |>.mono (fun x hx => by simpa only [hx,Pi.zero_apply] using (le_refl (0:ℝ)))
  | succ n ih =>
    have he : ((smoothing a ha : Base → Base)^[n+1]) f-(a/(a+C))^(n+1) • f=
        smoothing a ha (((smoothing a ha : Base → Base)^[n]) f-(a/(a+C))^n • f)+
        (a/(a+C))^n • (smoothing a ha f-(a/(a+C)) • f) := by
      rw [Function.iterate_succ_apply',map_sub,map_smul,pow_succ,smul_sub,smul_smul]
      module
    rw [he]
    exact add_nonnegative _ _ (HeatResolventSpectrum.smoothing_nonnegative ha _ ih)
      (smul_nonnegative _ (pow_nonneg hm _) _ (resolvent_barrier ha hC f g hfg hpos))

theorem heat_barrier (T : ℝ) (hT : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C) (f g : Base)
    (hfg : weakLaplacian f g) (hpos : ∀ᵐ x ∂baseMeasure,0 ≤ (g+C • f) x) :
    ∀ᵐ x ∂baseMeasure,0 ≤ (paperHeat T f-Real.exp (-T*C) • f) x := by
  rcases eq_or_lt_of_le hT with hz | hp
  · subst T
    simp only [paperHeat_zero,ContinuousLinearMap.id_apply,neg_zero,zero_mul,Real.exp_zero,one_smul,sub_self]
    exact Lp.coeFn_zero ℝ 2 baseMeasure |>.mono (fun x hx => by simpa only [hx,Pi.zero_apply] using (le_refl (0:ℝ)))
  · let u := fun n => HeatDirichletEuler.value T hp n f-
      ((1+(T*C)/(count T n:ℝ))⁻¹)^(count T n) • f
    have hscalar := ((tendsto_inverse (T*C)).comp (count_tendsto T)).smul_const f
    have hu : Tendsto u atTop (𝓝 (paperHeat T f-Real.exp (-T*C) • f)) := by
      simpa only [u,Function.comp_def,neg_mul] using (HeatDirichletEuler.tendsto_heat T hp f).sub hscalar
    apply HeatFourierFrameConvergence.nonnegative_limit u _ hu
    intro n
    have he := iterate_barrier (parameter_ge_one hp n) hC f g hfg hpos (count T n)
    rw [ratio hp hC n] at he
    exact he

end HeatSubeigenEuler
#check @HeatSubeigenEuler.smul_nonnegative
#print axioms HeatSubeigenEuler.smul_nonnegative
#check @HeatSubeigenEuler.add_nonnegative
#print axioms HeatSubeigenEuler.add_nonnegative
#check @HeatSubeigenEuler.resolvent_barrier
#print axioms HeatSubeigenEuler.resolvent_barrier
#check @HeatSubeigenEuler.iterate_barrier
#print axioms HeatSubeigenEuler.iterate_barrier
#check @HeatSubeigenEuler.heat_barrier
#print HeatSubeigenEuler.heat_barrier
#print axioms HeatSubeigenEuler.heat_barrier
