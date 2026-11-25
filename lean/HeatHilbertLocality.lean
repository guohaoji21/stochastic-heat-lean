import SHEStochastic.HilbertTerminalIto
import SHE.ItoLocalityTransport

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatHilbertLocality
open MeasureTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω ι κ E : Type*} [MeasurableSpace Ω] [Countable ι] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
  (b : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space ι ℝ) (E := ℝ) F μ T)

theorem locality (hlocal : StandardTerminalPastLocality J) :
    StandardTerminalPastLocality (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J) := by
  letI : MeasurableSpace (Space ι E) := borel _
  letI : BorelSpace (Space ι E) := ⟨rfl⟩
  letI : MeasurableSpace (Space ι ℝ) := borel _
  letI : BorelSpace (Space ι ℝ) := ⟨rfl⟩
  intro a A hA u
  have hz : (fun ω => SHEStochastic.HilbertTerminalIto.integral F μ T b J
      (eventProcess F μ T a A hA u) ω -
      A.indicator (SHEStochastic.HilbertTerminalIto.integral F μ T b J (post F μ T a u)) ω)
      =ᵐ[μ] (0 : Ω → E) := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    let M : Space ι E →L[ℝ] Space ι ℝ := mapCLM L
    have hc0 := L.coeFn_compLpL (SHEStochastic.HilbertTerminalIto.integral F μ T b J
      (eventProcess F μ T a A hA u))
    have hc1 := L.coeFn_compLpL (SHEStochastic.HilbertTerminalIto.integral F μ T b J
      (post F μ T a u))
    rw [SHEStochastic.HilbertTerminalIto.commutes] at hc0 hc1
    have he := hlocal a A hA ((M.compLpL 2 ((energyMeasure μ T).trim (predictable_le_product F))) u)
    rw [← SHE.ItoLocalityTransport.event_map F μ T M a A hA u,
      ← SHE.ItoLocalityTransport.post_map F μ T M a u] at he
    filter_upwards [hc0, hc1, he] with ω hc0 hc1 he
    change L (_ - _) = 0
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, map_sub]
      rw [Set.indicator_of_mem hω] at he
      exact sub_eq_zero.mpr (hc0.symm.trans (he.trans hc1))
    · rw [Set.indicator_of_notMem hω, map_sub, map_zero, sub_zero]
      rw [Set.indicator_of_notMem hω] at he
      exact hc0.symm.trans he
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

end HeatHilbertLocality

#check @HeatHilbertLocality.locality
#print axioms HeatHilbertLocality.locality
