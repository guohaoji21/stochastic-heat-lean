import HeatWeakDirichlet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatWeakSecondDerivative
open EllipticPdes MeasureTheory HeatWeakDirichlet HeatIntervalNormalization
open scoped RealInnerProductSpace

theorem partialCls_eq (φ : testFunctions domain) (v : ℝ) :
    H1Graph.partialCls volume domain φ v = v • H1Graph.gradCls volume domain φ := by
  apply Lp.ext
  filter_upwards [H1Graph.coeFn_partialCls (μ := volume) (Ω := domain) φ v,
    H1Graph.coeFn_gradCls (μ := volume) (Ω := domain) φ,
    Lp.coeFn_smul v (H1Graph.gradCls volume domain φ)] with x hp hg hs
  rw [hp, hs]
  simp only [Pi.smul_apply]
  rw [hg, ← EllipticPdes.inner_gradient_right]
  simp [Real.inner_apply, mul_comm]

theorem smulCls_eq (φ : testFunctions domain) (v : ℝ) :
    H1Graph.smulCls volume domain φ v = v • H1Graph.fnCls volume domain φ := by
  apply Lp.ext
  filter_upwards [H1Graph.coeFn_smulCls (μ := volume) (Ω := domain) φ v,
    H1Graph.coeFn_fnCls (μ := volume) (Ω := domain) φ,
    Lp.coeFn_smul v (H1Graph.fnCls volume domain φ)] with x hp hf hs
  rw [hp, hs]
  simp only [Pi.smul_apply]
  rw [hf]
  simp [smul_eq_mul, mul_comm]

theorem weakLaplacian_has_second_weak_derivative (f g : Base) (h : weakLaplacian f g) :
    ∃ U : H01, H1Graph.embL2 volume domain U = f ∧
      HasWeakFDerivOn ⟨domain, isOpen_Ioo⟩ (H1Graph.gradL (U : H1Graph volume domain))
        (fun x => innerSL ℝ (g x)) volume := by
  obtain ⟨U,hU,hform⟩ := h
  refine ⟨U,hU,?_⟩
  apply (H1Graph.mem_W12_iff_hasWeakFDerivOn isOpen_Ioo
    (H1Graph.mk (H1Graph.gradL (U : H1Graph volume domain)) g)).mp
  apply (H1Graph.mem_W12_iff _).mpr
  intro φ v
  have he := hform ⟨H1Graph.testGraphₗ volume domain φ, H1Graph.testGraphₗ_mem_H01 φ⟩
  have he' : inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradCls volume domain φ) =
      -inner ℝ g (H1Graph.fnCls volume domain φ) := he
  rw [H1Graph.inner_constraintVec, H1Graph.fnL_mk, H1Graph.gradL_mk]
  change inner ℝ (H1Graph.partialCls volume domain φ v) (H1Graph.gradL (U : H1Graph volume domain)) +
    inner ℝ (H1Graph.smulCls volume domain φ v) g = 0
  rw [partialCls_eq, smulCls_eq,
    real_inner_smul_left, real_inner_smul_left]
  have h1 := real_inner_comm (H1Graph.gradCls volume domain φ) (H1Graph.gradL (U : H1Graph volume domain))
  have h2 := real_inner_comm (H1Graph.fnCls volume domain φ) g
  have hz : inner ℝ (H1Graph.gradCls volume domain φ) (H1Graph.gradL (U : H1Graph volume domain)) +
      inner ℝ (H1Graph.fnCls volume domain φ) g = 0 := by linarith
  calc
    _ = v * (inner ℝ (H1Graph.gradCls volume domain φ) (H1Graph.gradL (U : H1Graph volume domain)) +
      inner ℝ (H1Graph.fnCls volume domain φ) g) := by ring
    _ = 0 := by rw [hz, mul_zero]

theorem weakLaplacian_of_second_weak_derivative (f g : Base)
    (U : H01) (hU : H1Graph.embL2 volume domain U = f)
    (hweak : HasWeakFDerivOn ⟨domain, isOpen_Ioo⟩ (H1Graph.gradL (U : H1Graph volume domain))
      (fun x => innerSL ℝ (g x)) volume) : weakLaplacian f g := by
  have hW := (H1Graph.mem_W12_iff_hasWeakFDerivOn isOpen_Ioo
    (H1Graph.mk (H1Graph.gradL (U : H1Graph volume domain)) g)).mpr hweak
  let L : H1Graph volume domain →L[ℝ] ℝ :=
    ((innerSL ℝ (H1Graph.gradL (U : H1Graph volume domain))).comp
      (H1Graph.gradL (μ := volume) (Ω := domain))) +
      ((innerSL ℝ (g : Lp ℝ 2 (volume.restrict domain))).comp
        (H1Graph.fnL (μ := volume) (Ω := domain)))
  have hclosed : IsClosed {W : H1Graph volume domain | L W = 0} :=
    isClosed_eq L.continuous continuous_const
  have htest : ∀ φ : testFunctions domain, L (H1Graph.testGraphₗ volume domain φ) = 0 := by
    intro φ
    have he := (H1Graph.mem_W12_iff _).mp hW φ (1 : ℝ)
    rw [H1Graph.inner_constraintVec, H1Graph.fnL_mk, H1Graph.gradL_mk] at he
    change inner ℝ (H1Graph.partialCls volume domain φ 1) (H1Graph.gradL (U : H1Graph volume domain)) +
      inner ℝ (H1Graph.smulCls volume domain φ 1) g = 0 at he
    rw [partialCls_eq, smulCls_eq, one_smul, one_smul] at he
    have h1 := real_inner_comm (H1Graph.gradCls volume domain φ) (H1Graph.gradL (U : H1Graph volume domain))
    have h2 := real_inner_comm (H1Graph.fnCls volume domain φ) g
    change inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradCls volume domain φ) +
      inner ℝ g (H1Graph.fnCls volume domain φ) = 0
    linarith
  refine ⟨U,hU,?_⟩
  intro V
  have hV := H1Graph.H01_subset_of_isClosed hclosed htest V.property
  change inner ℝ (H1Graph.gradL (U : H1Graph volume domain)) (H1Graph.gradL (V : H1Graph volume domain)) +
    inner ℝ g (H1Graph.embL2 volume domain V) = 0 at hV
  linarith

theorem weakLaplacian_iff_second_weak_derivative (f g : Base) : weakLaplacian f g ↔
    ∃ U : H01, H1Graph.embL2 volume domain U = f ∧
      HasWeakFDerivOn ⟨domain, isOpen_Ioo⟩ (H1Graph.gradL (U : H1Graph volume domain))
        (fun x => innerSL ℝ (g x)) volume := by
  constructor
  · exact weakLaplacian_has_second_weak_derivative f g
  · rintro ⟨U,hU,hw⟩
    exact weakLaplacian_of_second_weak_derivative f g U hU hw

end HeatWeakSecondDerivative
#check @HeatWeakSecondDerivative.partialCls_eq
#print axioms HeatWeakSecondDerivative.partialCls_eq
#check @HeatWeakSecondDerivative.smulCls_eq
#print axioms HeatWeakSecondDerivative.smulCls_eq
#check @HeatWeakSecondDerivative.weakLaplacian_has_second_weak_derivative
#print axioms HeatWeakSecondDerivative.weakLaplacian_has_second_weak_derivative

#check @HeatWeakSecondDerivative.weakLaplacian_of_second_weak_derivative
#print axioms HeatWeakSecondDerivative.weakLaplacian_of_second_weak_derivative
#check @HeatWeakSecondDerivative.weakLaplacian_iff_second_weak_derivative
#print axioms HeatWeakSecondDerivative.weakLaplacian_iff_second_weak_derivative
