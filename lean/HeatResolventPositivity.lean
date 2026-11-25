import HeatDirichletResolvent
import EllipticPdes.Sobolev.GraphLattice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatResolventPositivity
open MeasureTheory Filter EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolventForm HeatDirichletResolvent

theorem nonpositive {a : ℝ} (ha : 1≤a) (f : Base) (hf : ∀ᵐ x ∂baseMeasure, f x≤0) :
    ∀ᵐ x ∂baseMeasure, resolvent a ha f x≤0 := by
  let U := HeatDirichletResolventForm.lift a ha f
  obtain ⟨W,hW,hfn,hgr⟩ := H1Graph.exists_mem_H01_posPart_sub_const isOpen_Ioo U.property (le_refl (0:ℝ))
  let V : H01 := ⟨W,hW⟩
  have hfn' : (embed V : ℝ → ℝ)=ᵐ[baseMeasure] fun x => max (embed U x) 0 := by
    change (H1Graph.fnL W : ℝ → ℝ)=ᵐ[volume.restrict domain]
      fun x => max (H1Graph.fnL (U : H1Graph volume domain) x) 0
    simpa only [HeatWeakDirichlet.domain,sub_zero] using hfn
  have hgr' : (H1Graph.gradL (V : H1Graph volume domain) : ℝ → ℝ)=ᵐ[baseMeasure]
      fun x => if 0<embed U x then H1Graph.gradL (U : H1Graph volume domain) x else 0 := hgr
  have hinner : inner ℝ (embed U) (embed V)=‖embed V‖^2 := by
    rw [L2.inner_def,HeatIntervalNormalization.realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hfn'] with x hx
    simp only [Real.inner_apply,Real.norm_eq_abs,sq_abs]
    rw [hx]
    by_cases hu : 0≤embed U x
    · rw [max_eq_left hu];ring
    · rw [max_eq_right (le_of_not_ge hu)];ring
  have hgrad : inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradL (V : H1Graph volume domain))=
      ‖H1Graph.gradL (V : H1Graph volume domain)‖^2 := by
    rw [L2.inner_def,HeatIntervalNormalization.realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hgr'] with x hx
    simp only [Real.inner_apply,Real.norm_eq_abs,sq_abs]
    rw [hx]
    by_cases hu : 0<embed U x
    · rw [if_pos hu];ring
    · rw [if_neg hu];ring
  have hrhs : inner ℝ f (embed V)≤0 := by
    rw [L2.inner_def]
    apply integral_nonpos_of_ae
    filter_upwards [hf,hfn'] with x hfx hvx
    have hvn : 0≤embed V x := hvx ▸ le_max_right (embed U x) 0
    simpa only [Real.inner_apply,Pi.zero_apply,mul_comm] using mul_nonpos_of_nonpos_of_nonneg hfx hvn
  have he := variational ha f V
  change a*inner ℝ (embed U) (embed V)+
    inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradL (V : H1Graph volume domain))=inner ℝ f (embed V) at he
  rw [hinner,hgrad] at he
  have hz : embed V=0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖embed V‖,sq_nonneg ‖H1Graph.gradL (V : H1Graph volume domain)‖,norm_nonneg (embed V)])
  have hv0 : (embed V : ℝ → ℝ)=ᵐ[baseMeasure] fun _ => 0 := by
    rw [hz]
    exact Lp.coeFn_zero ℝ 2 baseMeasure
  filter_upwards [hfn',hv0] with x hx h0
  have hle := le_max_left (embed U x) 0
  rw [←hx,h0] at hle
  exact hle

theorem nonnegative {a : ℝ} (ha : 1≤a) (f : Base) (hf : ∀ᵐ x ∂baseMeasure, 0≤f x) :
    ∀ᵐ x ∂baseMeasure, 0≤resolvent a ha f x := by
  have hneg : ∀ᵐ x ∂baseMeasure, (-f) x≤0 := by
    filter_upwards [hf,Lp.coeFn_neg f] with x hx hn
    rw [hn]
    exact neg_nonpos.mpr hx
  have he := nonpositive ha (-f) hneg
  rw [map_neg] at he
  filter_upwards [he,Lp.coeFn_neg (resolvent a ha f)] with x hx hn
  rw [hn] at hx
  exact neg_nonpos.mp hx

end HeatResolventPositivity
#check @HeatResolventPositivity.nonpositive
#print axioms HeatResolventPositivity.nonpositive
#check @HeatResolventPositivity.nonnegative
#print HeatResolventPositivity.nonnegative
#print axioms HeatResolventPositivity.nonnegative
