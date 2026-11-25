import HeatBarrierChoice
import HeatConcreteSemigroupInput
import HeatCanonicalPredictableSolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatBarrierData
open MeasureTheory Set Filter HeatIntervalNormalization HeatPolynomialBarrier HeatWeakDirichlet
open HeatCanonicalPredictableSolution HeatConcreteSemigroupInput
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

theorem exists_barrier (u : ℝ → ℝ) (hu : Continuous u) (hpos : ∀ x,0≤u x) (hne : u≠0)
    (hsupp : tsupport u⊆Ioo (25/4:ℝ) (27/4)) (hmem : MemLp u 2 baseMeasure)
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖≤1)
    (hbone : ∀ x∈Ioo (25/4:ℝ) (27/4),b x=1) :
    ∃ C : ℝ,∃ f d : Base,0≤C ∧ f≠0 ∧ (∀ᵐ x ∂baseMeasure,0≤f x) ∧
      (∀ᵐ x ∂baseMeasure,f x≤hmem.toLp u x) ∧ weakLaplacian f d ∧
      (∀ᵐ x ∂baseMeasure,0 ≤ (d+C • f) x) ∧ noise b hb hbound f=f := by
  obtain ⟨a,c,δ,ha,hac,hc,hδ,hmin⟩ := HeatBarrierChoice.interval_inside hu hpos hne hsupp
  have ha0 : 0<a := by linarith
  have hc10 : c<10 := by linarith
  let α := δ/((c-a)^8+1)
  have hα : 0<α := div_pos hδ (by positivity)
  let f₀ := HeatBarrierGraph.f a c hac.le
  let d₀ := HeatBarrierGraph.g a c hac.le
  let C := 196/(c-a)^2
  have hf : ∀ᵐ x ∂baseMeasure,0 ≤ (α • f₀) x :=
    HeatSubeigenEuler.smul_nonnegative α hα.le f₀ (HeatBarrierGraph.nonnegative a c hac.le)
  have hfne : α • f₀≠0 := smul_ne_zero hα.ne' (HeatBarrierNonzero.lp_ne_zero hac ha0 hc10)
  have hle : ∀ᵐ x ∂baseMeasure,(α • f₀) x≤hmem.toLp u x := by
    filter_upwards [(HeatBarrierGraph.fMem a c hac.le).coeFn_toLp,hmem.coeFn_toLp,Lp.coeFn_smul α f₀] with x hx hu hs
    rw [hs]
    change α*f₀ x≤_
    change f₀ x=bump a c x at hx
    rw [hx,hu]
    exact HeatBarrierChoice.scaled_bound hac.le hδ u hpos hmin x
  have hgraph : weakLaplacian (α • f₀) (α • d₀) :=
    HeatWeakDirichletAlgebra.smul α f₀ d₀ (HeatBarrierGraph.weak_graph a c hac.le ha0 hc10)
  have hsub : ∀ᵐ x ∂baseMeasure,0 ≤ (α • d₀+C • (α • f₀)) x := by
    have he : α • d₀+C • (α • f₀)=α • (d₀+C • f₀) := by module
    rw [he]
    exact HeatSubeigenEuler.smul_nonnegative α hα.le _ (HeatBarrierGraph.subeigen a c hac.le hac)
  have hfixed : noise b hb hbound f₀=f₀ := by
    apply Lp.ext
    filter_upwards [(HeatBarrierGraph.fMem a c hac.le).coeFn_toLp,
      SHEStochastic.BoundedFieldOperator.operator_ae (HeatScalarMultiplier.field baseMeasure b hb hbound) f₀] with x hx hmul
    change f₀ x=bump a c x at hx
    change noise b hb hbound f₀ x=b x*f₀ x at hmul
    rw [hmul]
    by_cases hxin : x∈Icc a c
    · rw [hbone x ⟨ha.trans_le hxin.1,hxin.2.trans_lt hc⟩,one_mul]
    · have hz : bump a c x=0 := image_eq_zero_of_notMem_tsupport (fun h => hxin (support_subset a c hac.le h))
      rw [hx,hz,mul_zero]
  refine ⟨C,α • f₀,α • d₀,by positivity,hfne,hf,hle,hgraph,hsub,?_⟩
  rw [map_smul,hfixed]

end HeatBarrierData
#check @HeatBarrierData.exists_barrier
#print HeatBarrierData.exists_barrier
#print axioms HeatBarrierData.exists_barrier
