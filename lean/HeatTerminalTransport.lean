import HeatUnitHilbertStop
import SHE.StandardTerminalIto

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatTerminalTransport
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (T : ℝ≥0)

def fromUnitColumns (I : StandardTerminalIto (C := Space Unit E) (E := E) F μ T) :
    StandardTerminalIto (C := E) (E := E) F μ T := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let ν := (energyMeasure μ T).trim (predictable_le_product F)
  let V := HeatUnitHilbertLp.lpEquiv (E := E) ν
  refine { integral := I.integral.comp V.toLinearIsometry, adapted := ?_, centered := ?_ }
  · intro l v hv
    apply I.adapted l (V v)
    have ha := ae_eq_of_ae_eq_trim (HeatUnitHilbertLp.lpEquiv_ae ν v)
    filter_upwards [ha,hv] with p hp hstop htime
    rw [hp, hstop htime, map_zero]
  · intro v
    exact I.centered (V v)

end HeatTerminalTransport
#check @HeatTerminalTransport.fromUnitColumns
#print HeatTerminalTransport.fromUnitColumns
#print axioms HeatTerminalTransport.fromUnitColumns
