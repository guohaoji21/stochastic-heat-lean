import HeatBarrierGraph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatBarrierNonzero
open MeasureTheory Set Filter HeatIntervalNormalization HeatWeakDirichlet HeatPolynomialBarrier

theorem bump_positive {a b x : ℝ} (hx : x∈Ioo a b) : 0<bump a b x := by
  have hq : 0<q a b x := mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  rw [bump,(formulas_nonnegative hq.le).1]
  positivity

theorem bump_bound {a b : ℝ} (hab : a≤b) (x : ℝ) : bump a b x≤(b-a)^8 := by
  rcases le_total 0 (q a b x) with hq | hq
  · rw [bump,(formulas_nonnegative hq).1]
    have hqL : q a b x≤(b-a)^2 := by
      have he : (dq a b x)^2=(b-a)^2-4*q a b x := by unfold dq q;ring
      nlinarith [sq_nonneg (dq a b x)]
    calc
      _ ≤ ((b-a)^2)^4 := pow_le_pow_left₀ hq hqL 4
      _ = _ := by ring
  · rw [bump,(formulas_nonpositive hq).1]
    positivity

theorem lp_ne_zero {a b : ℝ} (hab : a<b) (ha : 0<a) (hb : b<10) :
    HeatBarrierGraph.f a b hab.le≠0 := by
  intro hz
  have he : (bump a b)=ᵐ[baseMeasure] (0 : ℝ → ℝ) := by
    have h := (HeatBarrierGraph.fMem a b hab.le).coeFn_toLp
    change (HeatBarrierGraph.f a b hab.le : ℝ → ℝ)=ᵐ[baseMeasure] bump a b at h
    rw [hz] at h
    exact h.symm.trans (Lp.coeFn_zero ℝ 2 baseMeasure)
  have hbad : ∀ᵐ x ∂baseMeasure,x∉Ioo a b := by
    filter_upwards [he] with x hx hxin
    have hp := bump_positive hxin
    rw [hx] at hp
    exact (lt_irrefl (0:ℝ)) hp
  have hzero : baseMeasure (Ioo a b)=0 := by
    simpa only [not_not,Set.setOf_mem_eq] using (ae_iff.mp hbad)
  have hsub : Ioo a b⊆Ioo (0:ℝ) 10 := fun x hx => ⟨ha.trans hx.1,hx.2.trans hb⟩
  rw [baseMeasure,Measure.restrict_apply measurableSet_Ioo,inter_eq_left.mpr hsub,Real.volume_Ioo] at hzero
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hzero

end HeatBarrierNonzero
#check @HeatBarrierNonzero.lp_ne_zero
#print HeatBarrierNonzero.lp_ne_zero
#print axioms HeatBarrierNonzero.lp_ne_zero
