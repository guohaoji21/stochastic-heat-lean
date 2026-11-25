import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section
namespace HeatIntegralCauchy
open MeasureTheory Filter
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω)

theorem pairing (f g : Ω → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g)=∫ ω,inner ℝ (f ω) (g ω) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with ω h1 h2
  rw [h1,h2]

theorem inner_square (f g : Ω → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω,inner ℝ (f ω) (g ω) ∂μ)^2 ≤ (∫ ω,‖f ω‖^2 ∂μ)*(∫ ω,‖g ω‖^2 ∂μ) := by
  have he := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [pairing μ f g hf hg,pairing μ f f hf hf,pairing μ g g hg hg] at he
  simpa only [real_inner_self_eq_norm_sq,pow_two] using he

end HeatIntegralCauchy
#check @HeatIntegralCauchy.pairing
#print axioms HeatIntegralCauchy.pairing
#check @HeatIntegralCauchy.inner_square
#print axioms HeatIntegralCauchy.inner_square
