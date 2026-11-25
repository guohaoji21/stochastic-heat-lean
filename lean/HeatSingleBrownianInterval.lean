import HeatHilbertIntervalExact
import HeatHilbertLocality
import SHEStochastic.StandardBrownianItoConstruction

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatSingleBrownianInterval
open MeasureTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
  (b : HilbertBasis κ ℝ E) (e : HilbertBasis Unit ℝ (Space Unit ℝ))
  (W : ℝ≥0 → Ω → ℝ)

theorem exists_integral_with_interval_cross
    (hc : ∀ ω, Continuous (fun t => W t ω))
    (ha : ∀ t, Measurable[F t] (W t))
    (hl : ∀ n (a : Fin n → Unit), FiniteBrownianLawOn F μ T (fun _ => W)
      (fun i j => if a i = a j then 1 else 0)) :
    letI : MeasurableSpace (Space Unit ℝ) := borel _
    letI : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
    ∃ J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T,
      StandardTerminalPastLocality J ∧
      (∀ t : ℝ≥0, t ≤ T →
        J.integral (StoppedItoInputs.stop F μ T t
          (RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) ())) =ᵐ[μ] W t) ∧
      ∀ (a c : ℝ≥0), a ≤ c → ∀ (u v : Process (E := Space Unit E) F μ T),
        μ[(fun ω => inner ℝ
          ((SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T c u) ω -
            (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T a u) ω)
          ((SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T c v) ω -
            (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T a v) ω)) | F a] =ᵐ[μ]
        μ[(fun ω => ∫ t in Set.Ioc a c, inner ℝ (u (t, ω)) (v (t, ω)) ∂timeMeasure T) | F a] := by
  letI : MeasurableSpace (Space Unit ℝ) := borel _
  letI : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (Space Unit E) := borel _
  letI : BorelSpace (Space Unit E) := ⟨rfl⟩
  have hbuild := SHEStochastic.standardBrownianItoConstruction F μ T e (fun _ => W)
  obtain ⟨J, hlocal, _, hcoordinates⟩ := hbuild (fun _ ω => hc ω) (fun _ t => ha t) hl
  refine ⟨J, hlocal, fun t ht => hcoordinates () t ht, ?_⟩
  intro a c hac u v
  exact HeatHilbertIntervalExact.conditional_cross_interval
    (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J)
    (HeatHilbertLocality.locality F μ T b J hlocal) hac u v

end HeatSingleBrownianInterval

#check @HeatSingleBrownianInterval.exists_integral_with_interval_cross
#print axioms HeatSingleBrownianInterval.exists_integral_with_interval_cross
