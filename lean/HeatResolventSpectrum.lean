import HeatResolventPositivity
import HeatFourierFrameMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatResolventSpectrum
open MeasureTheory Filter HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolvent HeatFourierFrame
open scoped Topology

theorem coordinate_resolvent {a : ℝ} (ha : 1≤a) (f : Base) (k : ℤ) :
    coordinate k (resolvent a ha f)=coordinate k f/(a+rate k) := by
  have he := weakLaplacian_symmetric _ _ _ _ (weak_graph ha f) (eigen k)
  have hc (x : Base) : inner ℝ x (vector k)=coordinate k x := real_inner_comm _ _
  rw [inner_sub_left,real_inner_smul_left,real_inner_smul_right] at he
  simp_rw [hc] at he
  have hd : a+rate k≠0 := ne_of_gt (by linarith [rate_nonnegative k])
  apply (eq_div_iff hd).mpr
  nlinarith

theorem coordinate_smoothing {a : ℝ} (ha : 1≤a) (f : Base) (k : ℤ) :
    coordinate k (smoothing a ha f)=(a/(a+rate k))*coordinate k f := by
  change coordinate k (a • resolvent a ha f)=_
  rw [map_smul,coordinate_resolvent]
  change a*(coordinate k f/(a+rate k))=_
  ring

theorem coordinate_iterate {a : ℝ} (ha : 1≤a) (f : Base) (k : ℤ) (n : ℕ) :
    coordinate k (((smoothing a ha : Base → Base)^[n]) f)=(a/(a+rate k))^n*coordinate k f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',coordinate_smoothing,ih,pow_succ]
    ring

theorem smoothing_nonnegative {a : ℝ} (ha : 1≤a) (f : Base) (hf : ∀ᵐ x ∂baseMeasure,0≤f x) :
    ∀ᵐ x ∂baseMeasure,0 ≤ smoothing a ha f x := by
  filter_upwards [HeatResolventPositivity.nonnegative ha f hf,Lp.coeFn_smul a (resolvent a ha f)] with x hx hs
  change 0≤(a • resolvent a ha f) x
  rw [hs]
  change 0≤a*resolvent a ha f x
  exact mul_nonneg (by linarith) hx

theorem iterate_nonnegative {a : ℝ} (ha : 1≤a) (f : Base) (hf : ∀ᵐ x ∂baseMeasure,0≤f x) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure,0≤((smoothing a ha : Base → Base)^[n]) f x := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact smoothing_nonnegative ha _ ih

theorem coordinate_heat (t : ℝ) (ht : 0≤t) (f : Base) (k : ℤ) :
    coordinate k (paperHeat t f)=Real.exp (-t*rate k)*coordinate k f := by
  rw [coordinate_coefficient,coordinate_coefficient]
  change (HeatSpectralDerivative.coefficient (measureEquiv (paperHeat t f)) k).im=_
  rw [HeatPhysicalGenerator.measureEquiv_heat]
  have he := HeatDirichletSpectrum.transported_fourier t ht (measureEquiv f) k
  have hi := congrArg Complex.im he
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,rate,HeatSpectralDerivative.coefficient,HeatPhysicalGenerator.coefficient] using hi

end HeatResolventSpectrum
#check @HeatResolventSpectrum.coordinate_resolvent
#print axioms HeatResolventSpectrum.coordinate_resolvent
#check @HeatResolventSpectrum.coordinate_smoothing
#print axioms HeatResolventSpectrum.coordinate_smoothing
#check @HeatResolventSpectrum.coordinate_iterate
#print axioms HeatResolventSpectrum.coordinate_iterate
#check @HeatResolventSpectrum.smoothing_nonnegative
#print axioms HeatResolventSpectrum.smoothing_nonnegative
#check @HeatResolventSpectrum.iterate_nonnegative
#print axioms HeatResolventSpectrum.iterate_nonnegative
#check @HeatResolventSpectrum.coordinate_heat
#print HeatResolventSpectrum.coordinate_heat
#print axioms HeatResolventSpectrum.coordinate_heat
