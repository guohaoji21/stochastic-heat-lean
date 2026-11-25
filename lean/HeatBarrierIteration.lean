import HeatSubeigenCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatBarrierIteration
open MeasureTheory Filter Set HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal BigOperators
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

variable (C : ℝ) (hC : 0≤C) (f d : Base) (hfd : HeatWeakDirichlet.weakLaplacian f d)
  (hsub : ∀ᵐ x ∂baseMeasure,0 ≤ (d+C • f) x)
  (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
  (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖≤1) (hpos : ∀ᵐ x ∂baseMeasure,0≤b x)
  (hfixed : noise b hb hbound f=f)

include hC hfd hsub hpos hfixed in
theorem reverse_lower (h : ℕ → ℝ≥0) (N : ℕ) (g : Base)
    (hgf : ∀ᵐ x ∂baseMeasure,f x≤g x) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure,(Real.exp (-C*∑ k∈Finset.range n,(h (N-k):ℝ)) • f) x≤
      HeatBackwardChain.reverseChain (HeatPaperCovariance.K b hb hbound) h N g n x := by
  induction n with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty,mul_zero,neg_zero,Real.exp_zero,one_smul,
      HeatBackwardChain.reverseChain] using hgf
  | succ n ih =>
    let a := Real.exp (-C*∑ k∈Finset.range n,(h (N-k):ℝ))
    let c := Real.exp (-C*(h (N-n):ℝ))
    have hi := HeatPaperPositivity.K_monotone b hb hbound hpos (h (N-n)) _ _ ih
    rw [map_smul] at hi
    have hl := HeatSubeigenCovariance.K_lower C hC f d hfd hsub b hb hbound hpos hfixed (h (N-n))
    have he : Real.exp (-C*∑ k∈Finset.range (n+1),(h (N-k):ℝ))=a*c := by
      rw [Finset.sum_range_succ,←Real.exp_add]
      congr 1
      ring
    rw [he,HeatBackwardChain.reverseChain]
    filter_upwards [hi,hl,Lp.coeFn_smul a (HeatPaperCovariance.K b hb hbound (h (N-n)) f),
      Lp.coeFn_smul c f,Lp.coeFn_smul (a*c) f] with x hix hlx h1 h2 h3
    change (a • HeatPaperCovariance.K b hb hbound (h (N-n)) f) x≤_ at hix
    change (c • f) x≤_ at hlx
    rw [h1] at hix
    rw [h2] at hlx
    rw [h3]
    change a*(HeatPaperCovariance.K b hb hbound (h (N-n)) f x)≤_ at hix
    change c*f x≤_ at hlx
    change (a*c)*f x≤_
    have ha : 0≤a := (Real.exp_pos _).le
    nlinarith

end HeatBarrierIteration
#check @HeatBarrierIteration.reverse_lower
#print HeatBarrierIteration.reverse_lower
#print axioms HeatBarrierIteration.reverse_lower
