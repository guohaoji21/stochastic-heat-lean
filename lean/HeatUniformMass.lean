import HeatBarrierData
import HeatBarrierIteration
import HeatL2Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatUniformMass
open MeasureTheory Set Filter HeatIntervalNormalization HeatCanonicalPredictableSolution
open scoped NNReal ENNReal BigOperators
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

theorem exists_lower_bound (u : ℝ → ℝ) (hu : Continuous u) (hpos : ∀ x,0≤u x) (hne : u≠0)
    (hsupp : tsupport u⊆Ioo (25/4:ℝ) (27/4)) (hmem : MemLp u 2 baseMeasure)
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖≤1)
    (hbpos : ∀ᵐ x ∂baseMeasure,0≤b x) (hbone : ∀ x∈Ioo (25/4:ℝ) (27/4),b x=1) (T : ℝ) :
    ∃ c : ℝ,0<c ∧ ∀ (h : ℕ → ℝ≥0) (N : ℕ),
      (∑ k∈Finset.range N,(h (N-k):ℝ))=T →
      c≤ inner ℝ (hmem.toLp u)
        (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N (hmem.toLp u) 0) := by
  obtain ⟨C,f,d,hC,hfne,hf,hfg,hgraph,hsub,hfixed⟩ :=
    HeatBarrierData.exists_barrier u hu hpos hne hsupp hmem b hb hbound hbone
  let G := hmem.toLp u
  have hg : ∀ᵐ x ∂baseMeasure,0≤G x := by
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
    exact hpos x
  have hinner : ‖f‖^2≤ inner ℝ G f := by
    have he := HeatL2Order.inner_mono f f G hf hfg
    rw [real_inner_self_eq_norm_sq,real_inner_comm G f] at he
    exact he
  refine ⟨Real.exp (-C*T)*‖f‖^2,mul_pos (Real.exp_pos _) (sq_pos_of_pos (norm_pos_iff.mpr hfne)),?_⟩
  intro h N hsum
  have hl := HeatBarrierIteration.reverse_lower C hC f d hgraph hsub b hb hbound hbpos hfixed h N G hfg N
  rw [hsum] at hl
  change ∀ᵐ x ∂baseMeasure,(Real.exp (-C*T) • f) x≤
    HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N G 0 x at hl
  have he := HeatL2Order.inner_mono G (Real.exp (-C*T) • f)
    (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N G 0) hg hl
  rw [real_inner_smul_right] at he
  exact (mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le).trans he

end HeatUniformMass
#check @HeatUniformMass.exists_lower_bound
#print HeatUniformMass.exists_lower_bound
#print axioms HeatUniformMass.exists_lower_bound
