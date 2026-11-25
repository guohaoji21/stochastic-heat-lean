import HeatIntervalNormalization
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatPaperAdjoint
open SHE HeatIntervalNormalization DyadicApproximation CircleHeat MeasureTheory AddCircle
open scoped RealInnerProductSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The coefficient proof is the one used by SHE.CircleL1Dual.heat_inner. -/
theorem circle_heat_inner (t : ℝ) (f g : CircleL2) :
    inner ℂ (heat t f) g = inner ℂ f (heat t g) := by
  rw [← fourierBasis.repr.inner_map_map, ← fourierBasis.repr.inner_map_map (x := f),
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [fourierBasis_repr, heat_fourierCoeff, RCLike.inner_apply', map_mul,
    heatWeight, Complex.conj_ofReal]
  ring

theorem realEmbed_inner_re (f g : RealL2) :
    (inner ℂ (realEmbed f) (realEmbed g)).re = inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  change Complex.reCLM (∫ x, inner ℂ (realEmbed f x) (realEmbed g x) ∂haarAddCircle) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner (realEmbed f) (realEmbed g))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [realEmbed_ae f, realEmbed_ae g] with x hf hg
  rw [hf, hg]
  simp [RCLike.inner_apply', Real.inner_apply, mul_comm]

theorem real_heat_inner (t : ℝ) (f g : RealL2) :
    inner ℝ (RealHeat.realHeat t f) g = inner ℝ f (RealHeat.realHeat t g) := by
  rw [← realEmbed_inner_re, ← realEmbed_inner_re f,
    RealHeat.realEmbed_realHeat, RealHeat.realEmbed_realHeat, circle_heat_inner]

theorem paper_heat_inner (t : ℝ) (f g : Base) :
    inner ℝ (paperHeat t f) g = inner ℝ f (paperHeat t g) := by
  rw [← paperOddEquiv.inner_map_map, ← paperOddEquiv.inner_map_map (x := f)]
  simp only [paperHeat_apply, paperOddEquiv.apply_symm_apply]
  change inner ℝ (RealHeat.realHeat (t/400) (paperOddEquiv f : RealL2)) (paperOddEquiv g : RealL2) =
    inner ℝ (paperOddEquiv f : RealL2) (RealHeat.realHeat (t/400) (paperOddEquiv g : RealL2))
  exact real_heat_inner _ _ _

theorem paperHeat_self_adjoint (t : ℝ) : IsSelfAdjoint (paperHeat t) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (paper_heat_inner t)

end HeatPaperAdjoint
#check @HeatPaperAdjoint.circle_heat_inner
#print axioms HeatPaperAdjoint.circle_heat_inner
#check @HeatPaperAdjoint.real_heat_inner
#print axioms HeatPaperAdjoint.real_heat_inner
#check @HeatPaperAdjoint.paper_heat_inner
#print axioms HeatPaperAdjoint.paper_heat_inner
#check @HeatPaperAdjoint.paperHeat_self_adjoint
#print axioms HeatPaperAdjoint.paperHeat_self_adjoint

#check @HeatPaperAdjoint.realEmbed_inner_re
#print axioms HeatPaperAdjoint.realEmbed_inner_re
