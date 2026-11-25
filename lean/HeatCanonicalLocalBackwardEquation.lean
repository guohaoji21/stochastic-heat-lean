import HeatLocalBackwardEquation
import HeatCanonicalNullComplete
import HeatCanonicalRightMartingaleRepresentation

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace HeatCanonicalLocalBackwardEquation

open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "P" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0, ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure P := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

variable {κ E : Type*} [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A positive step size works for every deterministic cell for the given
bounded drift operators. -/
theorem exists_step_size (A B : E →L[ℝ] E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, 0 ≤ l → l ≤ δ →
      2 * (‖A‖ ^ 2 * l ^ 2 + ‖B‖ ^ 2 * l) ≤ 1 / 4 := by
  let M := 1 + ‖A‖ ^ 2 + ‖B‖ ^ 2
  let δ := 1 / (8 * M)
  have hM₁ : 1 ≤ M := by
    dsimp [M]
    linarith [sq_nonneg ‖A‖, sq_nonneg ‖B‖]
  have hM : 0 < M := zero_lt_one.trans_le hM₁
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 8 * M)).mpr
    linarith
  refine ⟨δ, hδ, fun l hl hle => ?_⟩
  have hl₂ : l ^ 2 ≤ l := by
    nlinarith [mul_nonneg hl (sub_nonneg.mpr (hle.trans hδ₁))]
  calc
    _ ≤ 2 * (‖A‖ ^ 2 * l + ‖B‖ ^ 2 * l) := by
      gcongr
    _ ≤ 2 * M * l := by
      dsimp [M]
      nlinarith
    _ ≤ 2 * M * δ := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / 4 := by dsimp [δ]; field_simp; ring

/-- A local linear backward equation on the canonical Wiener space. In
particular both operators may be the matrices of a finite Galerkin system. -/
theorem exists_solution (H : ℝ≥0) (basis : HilbertBasis κ ℝ E) (A B : E →L[ℝ] E)
    {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H)
    (hshort : 2 * (‖A‖ ^ 2 * ((b : ℝ) - a) ^ 2 + ‖B‖ ^ 2 * ((b : ℝ) - a)) ≤ 1 / 4)
    (η : Lp E 2 P) (hη : AEStronglyMeasurable[F b] (η : C(ℝ≥0, ℝ) → E) P) :
    Nonempty (HeatLocalBackwardEquation.Solution
      (HeatTerminalNaturality.integral F P H basis (HeatCanonicalNative.scalar H)) A B a b η) :=
  HeatLocalBackwardEquation.exists_solution
    (HeatTerminalNaturality.integral F P H basis (HeatCanonicalNative.scalar H))
    (HeatTerminalNaturality.locality F P H basis (HeatCanonicalNative.scalar H) (HeatCanonicalNative.locality H))
    HeatCanonicalNullComplete.contains_nulls
    (HeatCanonicalRightMartingaleRepresentation.hilbert_centered_representation H basis)
    A B hab hb hshort η hη

end HeatCanonicalLocalBackwardEquation

#print axioms HeatCanonicalLocalBackwardEquation.exists_step_size
#print axioms HeatCanonicalLocalBackwardEquation.exists_solution
