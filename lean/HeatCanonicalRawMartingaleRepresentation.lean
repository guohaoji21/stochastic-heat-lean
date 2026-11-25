import HeatCanonicalUsualCross56
import MathFin.Foundations.MartingaleRepresentation

set_option autoImplicit false
noncomputable section

namespace HeatCanonicalRawMartingaleRepresentation

open MeasureTheory HeatCanonicalWiener56
open scoped NNReal

local instance : IsProbabilityMeasure wienerMeasure :=
  coordinate_preBrownian.isGaussianProcess.isProbabilityMeasure

abbrev RawInput (T : ℝ≥0) :=
  Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure_T (μ := wienerMeasure) T coordinate_measurable)

def rawIntegral (T : ℝ≥0) : RawInput T →L[ℝ] Lp ℝ 2 wienerMeasure :=
  MathFin.ItoIntegralCLM.itoIntegralCLM_T coordinate_preBrownian T coordinate_measurable

/-- Every centered real square-integrable variable in the raw canonical
Brownian filtration is represented by a predictable Itô input. -/
theorem centered_representation (T : ℝ≥0) (X : Lp ℝ 2 wienerMeasure)
    (hX : AEStronglyMeasurable[HeatCanonicalUsual56.naturalFiltration T] (X : C(ℝ≥0, ℝ) → ℝ) wienerMeasure)
    (hcenter : ∫ ω, X ω ∂wienerMeasure = 0) :
    ∃ v : RawInput T, rawIntegral T v = X :=
  MathFin.mem_range_itoIntegralCLM_T_of_centered coordinate_preBrownian coordinate_measurable
    (fun ω => ω.continuous) T X hX hcenter

end HeatCanonicalRawMartingaleRepresentation

#print axioms HeatCanonicalRawMartingaleRepresentation.centered_representation
