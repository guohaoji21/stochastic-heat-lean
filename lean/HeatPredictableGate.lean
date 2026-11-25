import SHE.PastItoAlgebra
import SHE.PredictableExponential

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatPredictableGate
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (s : Set (ℝ≥0 × Ω)) (hs : MeasurableSet[F.predictable] s)

def gate (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  ((Lp.memLp u).indicator hs.nullMeasurableSet).toLp (s.indicator u)

theorem gate_ae (u : Process (E := E) F μ H) : gate F μ H s hs u=ᵐ[energyMeasure μ H] s.indicator u :=
  ae_eq_of_ae_eq_trim ((Lp.memLp u).indicator hs.nullMeasurableSet).coeFn_toLp

theorem norm_le (u : Process (E := E) F μ H) : ‖gate F μ H s hs u‖≤‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [((Lp.memLp u).indicator hs.nullMeasurableSet).coeFn_toLp] with p hp
  change gate F μ H s hs u p=s.indicator u p at hp
  change ‖gate F μ H s hs u p‖≤‖u p‖
  rw [hp]
  exact norm_indicator_le_norm_self _ _

theorem sub (u v : Process (E := E) F μ H) :
    gate F μ H s hs (u-v)=gate F μ H s hs u-gate F μ H s hs v := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [gate_ae F μ H s hs (u-v),gate_ae F μ H s hs u,gate_ae F μ H s hs v,
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v),ae_eq_of_ae_eq_trim (Lp.coeFn_sub (gate F μ H s hs u) (gate F μ H s hs v))] with p hu hv hw hi ho
  rw [hu,ho]
  change s.indicator (u-v) p=gate F μ H s hs u p-gate F μ H s hs v p
  rw [hv,hw]
  by_cases hp : p∈s
  · rw [indicator_of_mem hp,indicator_of_mem hp,indicator_of_mem hp]
    exact hi
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,indicator_of_notMem hp,sub_self]

theorem idempotent (u : Process (E := E) F μ H) :
    gate F μ H s hs (gate F μ H s hs u)=gate F μ H s hs u := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [gate_ae F μ H s hs (gate F μ H s hs u),gate_ae F μ H s hs u] with p h1 h2
  rw [h1]
  by_cases hp : p∈s
  · exact indicator_of_mem hp _
  · rw [indicator_of_notMem hp,h2,indicator_of_notMem hp]

theorem scale (γ : ℝ) (u : Process (E := E) F μ H) :
    gate F μ H s hs (PredictableExponential.scale F μ H γ u)=
      PredictableExponential.scale F μ H γ (gate F μ H s hs u) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [gate_ae F μ H s hs (PredictableExponential.scale F μ H γ u),
    PredictableExponential.ae F μ H γ u,PredictableExponential.ae F μ H γ (gate F μ H s hs u),
    gate_ae F μ H s hs u] with p h1 h2 h3 h4
  rw [h1,h3]
  by_cases hp : p∈s
  · rw [indicator_of_mem hp,h2,h4,indicator_of_mem hp]
  · rw [indicator_of_notMem hp,h4,indicator_of_notMem hp,smul_zero]

theorem eq_zero (u : Process (E := E) F μ H)
    (hu : ∀ᵐ p ∂energyMeasure μ H, p∈s → u p=0) : gate F μ H s hs u=0 := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [gate_ae F μ H s hs u,hu,ae_eq_of_ae_eq_trim (Lp.coeFn_zero E 2 _)] with p hg hu hz
  rw [hg,hz]
  change s.indicator u p=0
  by_cases hp : p∈s
  · rw [indicator_of_mem hp,hu hp]
  · rw [indicator_of_notMem hp]

end HeatPredictableGate
#check @HeatPredictableGate.gate_ae
#print axioms HeatPredictableGate.gate_ae
#check @HeatPredictableGate.norm_le
#print axioms HeatPredictableGate.norm_le
#check @HeatPredictableGate.sub
#print axioms HeatPredictableGate.sub
#check @HeatPredictableGate.idempotent
#print axioms HeatPredictableGate.idempotent
#check @HeatPredictableGate.scale
#print axioms HeatPredictableGate.scale
#check @HeatPredictableGate.eq_zero
#print HeatPredictableGate.eq_zero
#print axioms HeatPredictableGate.eq_zero
