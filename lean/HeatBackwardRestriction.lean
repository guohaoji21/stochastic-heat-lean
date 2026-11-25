import HeatBackwardGluing

set_option autoImplicit false
noncomputable section
namespace HeatBackwardRestriction
open MeasureTheory
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Measure Ω) (S : ℝ≥0 → E →L[ℝ] E)
  (D I : ℝ≥0 → ℝ≥0 → Ω → E) (z : ℝ≥0 → Ω → E)

theorem restrict (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    {a c b : ℝ≥0} (hac : a≤c) (hcb : c≤b)
    (hD : D a b=ᵐ[μ] fun ω => D a c ω+S (c-a) (D c b ω))
    (hI : I a b=ᵐ[μ] fun ω => I a c ω+S (c-a) (I c b ω))
    (ha : HeatBackwardGluing.Equation μ S D I z a b)
    (hc : HeatBackwardGluing.Equation μ S D I z c b) :
    HeatBackwardGluing.Equation μ S D I z a c := by
  filter_upwards [hD,hI,ha,hc] with ω hd hi ha hc
  rw [ha,hc,map_sub,map_add,hd,hi]
  have ht : (c-a)+(b-c)=b-a := by rw [add_comm];exact tsub_add_tsub_cancel hcb hac
  have hs := congrArg (fun A : E →L[ℝ] E => A (z b ω)) (hsem (c-a) (b-c))
  rw [ht] at hs
  change S (b-a) (z b ω)=S (c-a) (S (b-c) (z b ω)) at hs
  rw [hs]
  abel

end HeatBackwardRestriction
#check @HeatBackwardRestriction.restrict
#print HeatBackwardRestriction.restrict
#print axioms HeatBackwardRestriction.restrict
