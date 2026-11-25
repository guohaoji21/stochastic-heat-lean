import HeatPaperCovariance
import HeatBackwardChain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatOriginalTerminalChain
open MeasureTheory Set HeatIntervalNormalization HeatCanonicalPredictableSolution
open scoped NNReal ENNReal

theorem noise_fixes_initial (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1) (hbone : ∀ x∈Ioo (25/4:ℝ) (27/4),b x=1)
    (g : ℝ → ℝ) (hsupp : tsupport g⊆Ioo (25/4:ℝ) (27/4)) (hg : MemLp g 2 baseMeasure) :
    noise b hb hbound (hg.toLp g)=hg.toLp g := by
  apply Lp.ext
  filter_upwards [hg.coeFn_toLp,
    SHEStochastic.BoundedFieldOperator.operator_ae (HeatScalarMultiplier.field baseMeasure b hb hbound) (hg.toLp g)] with x hx hm
  change noise b hb hbound (hg.toLp g) x=b x*(hg.toLp g) x at hm
  rw [hm,hx]
  by_cases hxin : x∈Ioo (25/4:ℝ) (27/4)
  · rw [hbone x hxin,one_mul]
  · have hg0 : g x=0 := image_eq_zero_of_notMem_tsupport (fun h => hxin (hsupp h))
    rw [hg0,mul_zero]

theorem zero_covariance_fixes_initial (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1) (hbone : ∀ x∈Ioo (25/4:ℝ) (27/4),b x=1)
    (g : ℝ → ℝ) (hsupp : tsupport g⊆Ioo (25/4:ℝ) (27/4)) (hg : MemLp g 2 baseMeasure) :
    HeatPaperCovariance.K b hb hbound 0 (hg.toLp g)=hg.toLp g := by
  rw [HeatPaperCovariance.K_zero,noise_fixes_initial b hb hbound hbone g hsupp hg]

end HeatOriginalTerminalChain
#check @HeatOriginalTerminalChain.noise_fixes_initial
#print axioms HeatOriginalTerminalChain.noise_fixes_initial
#check @HeatOriginalTerminalChain.zero_covariance_fixes_initial
#print axioms HeatOriginalTerminalChain.zero_covariance_fixes_initial
