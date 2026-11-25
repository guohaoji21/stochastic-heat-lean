import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section
namespace HeatL2Integrability
open MeasureTheory
open scoped ENNReal
variable {P E : Type*} [MeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ν : Measure P)

theorem inner (f g : P → E) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun p => inner ℝ (f p) (g p)) ν := by
  apply (L2.integrable_inner (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with p hf hg
  rw [hf,hg]

end HeatL2Integrability
#check @HeatL2Integrability.inner
#print axioms HeatL2Integrability.inner
