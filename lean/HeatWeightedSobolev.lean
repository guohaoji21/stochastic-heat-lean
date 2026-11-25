import HeatExponentialWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatWeightedSobolev
open MeasureTheory Filter EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatExponentialWeight
open scoped NNReal ENNReal

def graph (a : ℝ) : H1Graph volume domain →L[ℝ] H1Graph volume domain :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Base Base).symm.toContinuousLinearMap.comp
    (((weight a).comp (H1Graph.fnL (μ := volume) (Ω := domain))).prod
      (((weight a).comp (H1Graph.gradL (μ := volume) (Ω := domain)))+
        a • ((weight a).comp (H1Graph.fnL (μ := volume) (Ω := domain)))))

theorem fn_graph (a : ℝ) (U : H1Graph volume domain) : H1Graph.fnL (graph a U)=weight a (H1Graph.fnL U) := rfl

theorem grad_graph (a : ℝ) (U : H1Graph volume domain) :
    H1Graph.gradL (graph a U)=weight a (H1Graph.gradL U)+a • weight a (H1Graph.fnL U) := rfl

def test (a : ℝ) (φ : testFunctions domain) : testFunctions domain := by
  let ψ := fun x => value a x*(φ : ℝ → ℝ) x
  have hsup : tsupport ψ⊆tsupport (φ : ℝ → ℝ) := tsupport_mul_subset_right
  refine ⟨ψ,?_,(φ.property.2.1).of_isClosed_subset (isClosed_tsupport _) hsup,hsup.trans φ.property.2.2⟩
  exact (by unfold value;fun_prop : ContDiff ℝ (⊤:ℕ∞) (value a)).mul φ.property.1

theorem test_gradient (a : ℝ) (φ : testFunctions domain) (x : ℝ) :
    gradient (test a φ : ℝ → ℝ) x=
      value a x*gradient (φ : ℝ → ℝ) x+a*(value a x*(φ : ℝ → ℝ) x) := by
  have hw : HasDerivAt (value a) (value a x*a) x := by
    have hh := (Real.hasDerivAt_exp (a*x)).comp x ((hasDerivAt_id x).const_mul a)
    convert hh using 1
    · funext y;rfl
    · simp only [value,id_eq];ring
  have hp := (φ.property.1.differentiable (by simp) x).hasDerivAt
  have hd := hw.mul hp
  rw [gradient_eq_deriv',gradient_eq_deriv']
  have he : deriv (test a φ : ℝ → ℝ) x=Real.exp (a*x)*a*(φ : ℝ → ℝ) x+Real.exp (a*x)*deriv (φ : ℝ → ℝ) x := hd.deriv
  rw [he]
  unfold value
  ring

theorem graph_test (a : ℝ) (φ : testFunctions domain) :
    graph a (H1Graph.testGraphₗ volume domain φ)=H1Graph.testGraphₗ volume domain (test a φ) := by
  apply H1Graph.ext
  · change weight a (H1Graph.fnCls volume domain φ)=H1Graph.fnCls volume domain (test a φ)
    apply Lp.ext
    filter_upwards [weight_ae a (H1Graph.fnCls volume domain φ),
      H1Graph.coeFn_fnCls (μ := volume) (Ω := domain) φ,
      H1Graph.coeFn_fnCls (μ := volume) (Ω := domain) (test a φ)] with x hw hφ ht
    rw [hw,hφ,ht]
    rfl
  · change weight a (H1Graph.gradCls volume domain φ)+a • weight a (H1Graph.fnCls volume domain φ)=H1Graph.gradCls volume domain (test a φ)
    apply Lp.ext
    filter_upwards [weight_ae a (H1Graph.gradCls volume domain φ),weight_ae a (H1Graph.fnCls volume domain φ),
      H1Graph.coeFn_gradCls (μ := volume) (Ω := domain) φ,H1Graph.coeFn_fnCls (μ := volume) (Ω := domain) φ,
      H1Graph.coeFn_gradCls (μ := volume) (Ω := domain) (test a φ),
      Lp.coeFn_add (weight a (H1Graph.gradCls volume domain φ)) (a • weight a (H1Graph.fnCls volume domain φ)),
      Lp.coeFn_smul a (weight a (H1Graph.fnCls volume domain φ))] with x hw hg hφ ht hψ hsum hsmul
    rw [hsum]
    simp only [Pi.add_apply]
    rw [hsmul]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hw,hg,hφ,ht,hψ]
    exact (test_gradient a φ x).symm

theorem graph_mem_H01 (a : ℝ) (U : H01) : graph a U ∈ H1Graph.H01 volume domain := by
  apply H1Graph.H01_subset_of_isClosed (H1Graph.isClosed_H01.preimage (graph a).continuous) _ U.property
  intro φ
  change graph a (H1Graph.testGraphₗ volume domain φ)∈H1Graph.H01 volume domain
  rw [graph_test]
  exact H1Graph.testGraphₗ_mem_H01 _

def map (a : ℝ) (U : H01) : H01 := ⟨graph a U,graph_mem_H01 a U⟩

end HeatWeightedSobolev
#check @HeatWeightedSobolev.graph_mem_H01
#print HeatWeightedSobolev.graph_mem_H01
#print axioms HeatWeightedSobolev.graph_mem_H01
