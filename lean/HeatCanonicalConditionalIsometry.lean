import HeatCanonicalNative
import HeatHilbertIntervalExact
import HeatTerminalNaturality

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatCanonicalConditionalIsometry
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0,ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {κ E : Type*} [Countable κ] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (T : ℝ≥0) (basis : HilbertBasis κ ℝ E)
local notation "I" => HeatTerminalNaturality.integral F μ T basis (HeatCanonicalNative.scalar T)

theorem interval (a c : ℝ≥0) (hac : a ≤ c) (u v : Process (E := E) F μ T) :
    μ[(fun ω => inner ℝ
      ((I).integral (StoppedItoInputs.stop F μ T c u) ω-(I).integral (StoppedItoInputs.stop F μ T a u) ω)
      ((I).integral (StoppedItoInputs.stop F μ T c v) ω-(I).integral (StoppedItoInputs.stop F μ T a v) ω)) | F a]=ᵐ[μ]
      μ[(fun ω => ∫ s in Set.Ioc a c,inner ℝ (u (s,ω)) (v (s,ω)) ∂timeMeasure T) | F a] :=
  HeatHilbertIntervalExact.conditional_cross_interval I
    (HeatTerminalNaturality.locality F μ T basis (HeatCanonicalNative.scalar T) (HeatCanonicalNative.locality T)) hac u v

theorem square (a c : ℝ≥0) (hac : a ≤ c) (u : Process (E := E) F μ T) :
    μ[(fun ω => ‖(I).integral (StoppedItoInputs.stop F μ T c u) ω-
      (I).integral (StoppedItoInputs.stop F μ T a u) ω‖^2) | F a]=ᵐ[μ]
      μ[(fun ω => ∫ s in Set.Ioc a c,‖u (s,ω)‖^2 ∂timeMeasure T) | F a] := by
  simpa only [real_inner_self_eq_norm_sq] using interval T basis a c hac u u

end HeatCanonicalConditionalIsometry
#check @HeatCanonicalConditionalIsometry.interval
#print axioms HeatCanonicalConditionalIsometry.interval
#check @HeatCanonicalConditionalIsometry.square
#print axioms HeatCanonicalConditionalIsometry.square
