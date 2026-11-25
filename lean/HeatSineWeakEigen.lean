import HeatSineH01

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatSineWeakEigen
open MeasureTheory EllipticPdes HeatSineH01 HeatWeakDirichlet HeatIntervalNormalization
open scoped RealInnerProductSpace

theorem cosine_hasDerivAt (k x : ℝ) :
    HasDerivAt (fun y : ℝ => k*Real.cos (k*y)) (-(k^2)*Real.sin (k*x)) x := by
  have h := ((Real.hasDerivAt_cos (k*x)).comp x ((hasDerivAt_id x).const_mul k)).const_mul k
  convert h using 1
  · funext y; rfl
  · ring

theorem sine_weak_eigenpair (k : ℝ) (hend : Real.sin (k*10) = 0) :
    weakLaplacian (sine k) ((-(k^2)) • sine k) := by
  let U : H01 := ⟨H1Graph.mk (sine k) (sineGradient k), sineGraph_mem_H01 k hend⟩
  apply HeatWeakSecondDerivative.weakLaplacian_of_second_weak_derivative _ _ U rfl
  change HasWeakFDerivOn ⟨domain, isOpen_Ioo⟩ (sineGradient k)
    (fun x => innerSL ℝ (((-(k^2)) • sine k) x)) volume
  have hclass : HasWeakFDerivOn ⟨domain, isOpen_Ioo⟩ (fun x : ℝ => k*Real.cos (k*x))
      (fderiv ℝ (fun x : ℝ => k*Real.cos (k*x))) volume :=
    hasWeakFDerivOn_fderiv (by fun_prop)
  apply hclass.congr_ae (sineGradient_ae k).symm
  filter_upwards [sine_ae k, Lp.coeFn_smul (-(k^2)) (sine k)] with x hs hm
  rw [(cosine_hasDerivAt k x).hasFDerivAt.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rw [hm]
  simp only [Pi.smul_apply, hs, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  simp [Real.inner_apply, mul_comm, mul_left_comm, mul_assoc]

theorem sine_integration_by_parts (f g : Base) (h : weakLaplacian f g)
    (k : ℝ) (hend : Real.sin (k*10) = 0) :
    inner ℝ g (sine k) = -(k^2) * inner ℝ f (sine k) := by
  have he := weakLaplacian_symmetric f g (sine k) ((-(k^2)) • sine k) h (sine_weak_eigenpair k hend)
  simpa only [inner_smul_right, smul_eq_mul] using he

theorem frequency_boundary (n : ℤ) : Real.sin ((Real.pi*(n:ℝ)/10)*10) = 0 := by
  rw [show (Real.pi*(n:ℝ)/10)*10 = (n:ℝ)*Real.pi by ring]
  exact Real.sin_int_mul_pi n

theorem sine_modal_identity (f g : Base) (h : weakLaplacian f g) (n : ℤ) :
    inner ℝ g (sine (Real.pi*(n:ℝ)/10)) =
      -((Real.pi*(n:ℝ)/10)^2) * inner ℝ f (sine (Real.pi*(n:ℝ)/10)) :=
  sine_integration_by_parts f g h _ (frequency_boundary n)

end HeatSineWeakEigen
#check @HeatSineWeakEigen.cosine_hasDerivAt
#print axioms HeatSineWeakEigen.cosine_hasDerivAt
#check @HeatSineWeakEigen.sine_weak_eigenpair
#print axioms HeatSineWeakEigen.sine_weak_eigenpair
#check @HeatSineWeakEigen.sine_integration_by_parts
#print axioms HeatSineWeakEigen.sine_integration_by_parts
#check @HeatSineWeakEigen.frequency_boundary
#print axioms HeatSineWeakEigen.frequency_boundary
#check @HeatSineWeakEigen.sine_modal_identity
#print axioms HeatSineWeakEigen.sine_modal_identity
