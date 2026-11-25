import HeatTerminalNaturality

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatPredictableLinearMap
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def map (A : E →L[ℝ] E) (u : Process (E := E) F μ H) : Process (E := E) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (A.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u

theorem map_ae (A : E →L[ℝ] E) (u : Process (E := E) F μ H) :
    map F μ H A u=ᵐ[energyMeasure μ H] fun p => A (u p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ae_eq_of_ae_eq_trim (A.coeFn_compLpL u)

theorem contraction (A : E →L[ℝ] E) (hA : ∀ x, ‖A x‖≤‖x‖) (u : Process (E := E) F μ H) :
    ‖map F μ H A u‖≤‖u‖ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [A.coeFn_compLpL u] with p hp
  change map F μ H A u p=A (u p) at hp
  rw [hp]
  exact hA _

theorem stop_commutes (A : E →L[ℝ] E) (u : Process (E := E) F μ H) (T : ℝ≥0) :
    map F μ H A (StoppedItoInputs.stop F μ H T u)=StoppedItoInputs.stop F μ H T (map F μ H A u) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [map_ae F μ H A (StoppedItoInputs.stop F μ H T u),
    StoppedItoInputs.stop_ae F μ H T u,StoppedItoInputs.stop_ae F μ H T (map F μ H A u),map_ae F μ H A u] with p hm hs ht hmu
  rw [hm,ht]
  by_cases hp : p∈StoppedItoInputs.before (T:ℝ)
  · rw [Set.indicator_of_mem hp,hs,Set.indicator_of_mem hp,hmu]
  · rw [Set.indicator_of_notMem hp,hs,Set.indicator_of_notMem hp,map_zero]

end HeatPredictableLinearMap
#check @HeatPredictableLinearMap.map_ae
#print axioms HeatPredictableLinearMap.map_ae
#check @HeatPredictableLinearMap.contraction
#print axioms HeatPredictableLinearMap.contraction
#check @HeatPredictableLinearMap.stop_commutes
#print HeatPredictableLinearMap.stop_commutes
#print axioms HeatPredictableLinearMap.stop_commutes
