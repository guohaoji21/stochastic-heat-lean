import HeatTerminalNaturality

set_option autoImplicit false
noncomputable section
namespace HeatLpAdaptedMap
open MeasureTheory
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω)

theorem map (A : E →L[ℝ] E) (t : ℝ≥0) (X : Lp E 2 μ) (hX : AEStronglyMeasurable[F t] X μ) :
    AEStronglyMeasurable[F t] ((A.compLpL 2 μ) X) μ :=
  (A.continuous.comp_aestronglyMeasurable hX).congr (A.coeFn_compLpL X).symm

end HeatLpAdaptedMap
#check @HeatLpAdaptedMap.map
#print HeatLpAdaptedMap.map
#print axioms HeatLpAdaptedMap.map
