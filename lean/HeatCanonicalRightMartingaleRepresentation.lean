import HeatCanonicalRawMartingaleRepresentation
import HeatRightPastRepresentative
import HeatRawItoCompatibility
import HeatCanonicalNative
import HeatTerminalItoCompression
import HeatHilbertMartingaleRepresentation
import SHEStochastic.NativeIntegralUniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace HeatCanonicalRightMartingaleRepresentation

open MeasureTheory HeatCanonicalWiener56 HeatCanonicalUsual56 HeatCompletedSpace56
open scoped NNReal

local notation "P" => HeatCanonicalUsualCross56.completedWiener

private theorem ambient_le :
    (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) ≤ completedMeasurableSpace wienerMeasure :=
  ambient_le_completion wienerMeasure

private def rawFiltration : Filtration ℝ≥0 (completedMeasurableSpace wienerMeasure) :=
  completedAmbientFiltration wienerMeasure naturalFiltration

private theorem complete_wiener : Measure.IsComplete P := completedMeasure_isComplete wienerMeasure

local instance : MeasurableSpace C(ℝ≥0, ℝ) := completedMeasurableSpace wienerMeasure
local instance : IsProbabilityMeasure P := HeatCanonicalUsualCross56.completedWiener_probability
local instance : Measure.IsComplete P := complete_wiener

private theorem coordinate_measurable (t : ℝ≥0) : Measurable (coordinate t) :=
  (HeatCanonicalWiener56.coordinate_measurable t).mono ambient_le le_rfl

abbrev RawInput (H : ℝ≥0) := Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure_T (μ := P) H coordinate_measurable)

def rawIntegral (H : ℝ≥0) : RawInput H →L[ℝ] Lp ℝ 2 P :=
  MathFin.ItoIntegralCLM.itoIntegralCLM_T (μ := P)
    coordinate_filtered_brownian.toIsPreBrownianReal H coordinate_measurable

/-- A centered square-integrable terminal variable for the usual filtration
has a raw Itô representation on any strictly larger time horizon. Both
representations use the completed canonical Wiener measure. -/
theorem centered_representation_later {T H : ℝ≥0} (hTH : T < H) (X : Lp ℝ 2 P)
    (hX : AEStronglyMeasurable[usualFiltration T] (X : C(ℝ≥0, ℝ) → ℝ) P)
    (hcenter : ∫ ω, X ω ∂P = 0) : ∃ u : RawInput H, rawIntegral H u = X := by
  change AEStronglyMeasurable[(HeatNullAugmentation56.nullAugmentation (μ := P) rawFiltration).rightCont T]
    (X : C(ℝ≥0, ℝ) → ℝ) P at hX
  have hraw := HeatRightPastRepresentative.right_past rawFiltration hTH hX
  change AEStronglyMeasurable[MathFin.ItoIntegralL2.natFiltration coordinate_measurable H]
    (X : C(ℝ≥0, ℝ) → ℝ) P at hraw
  exact MathFin.mem_range_itoIntegralCLM_T_of_centered (μ := P)
    coordinate_filtered_brownian.toIsPreBrownianReal coordinate_measurable
    (fun ω => ω.continuous) H X hraw hcenter

private theorem raw_le_usual (t : ℝ≥0) :
    MathFin.ItoIntegralL2.natFiltration coordinate_measurable t ≤ usualFiltration t := by
  let F := HeatNullAugmentation56.nullAugmentation (μ := P) rawFiltration
  change rawFiltration t ≤ F.rightCont t
  exact (show rawFiltration t ≤ F t from le_sup_left).trans (F.le_rightCont t)

open SHE SHE.PredictableL2 SHE.HilbertColumns SHEStochastic
open scoped ENNReal

local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

/-- The earlier usual-filtration terminal variable is represented by the
native scalar integral at the larger horizon. -/
theorem native_centered_representation_later {T H : ℝ≥0} (hTH : T < H) (X : Lp ℝ 2 P)
    (hX : AEStronglyMeasurable[usualFiltration T] (X : C(ℝ≥0, ℝ) → ℝ) P)
    (hcenter : ∫ ω, X ω ∂P = 0) :
    ∃ v : Process (E := Space Unit ℝ) usualFiltration P H, (HeatCanonicalNative.scalar H).integral v = X := by
  obtain ⟨u, hu⟩ := centered_representation_later hTH X hX hcenter
  let Q := (HeatCanonicalNative.family H).toCoordinates
  let v := HeatRawItoCompatibility.embed (μ := P) coordinate_measurable raw_le_usual H u
  let ν := FiniteScalarIto.inputMeasure usualFiltration P H
  letI : MeasurableSpace (ℝ≥0 × C(ℝ≥0, ℝ)) := usualFiltration.predictable
  let w := L2HilbertSum.lift ν (ColumnsHilbertSum.unit HeatTerminalBrownian.e ()) v
  refine ⟨NativeInputEquiv.inverse usualFiltration P H w, ?_⟩
  change FiniteCylindricalIto.rawIntegral Q HeatTerminalBrownian.e
    (FiniteCylindricalIto.processTransport (NativeInputEquiv.inverse usualFiltration P H w)) = X
  rw [NativeInputEquiv.transport_inverse]
  change FiniteCylindricalIto.rawIntegral Q HeatTerminalBrownian.e
    (L2HilbertSum.lift ν (ColumnsHilbertSum.unit HeatTerminalBrownian.e ()) v) = X
  rw [FiniteCylindricalIto.rawIntegral_unit]
  exact (HeatRawItoCompatibility.integral (μ := P) coordinate_measurable raw_le_usual
    coordinate_filtered_brownian.toIsPreBrownianReal H Q () rfl u).trans hu

/-- The project's canonical usual-filtration scalar integral represents every
centered square-integrable terminal variable at its original horizon. -/
theorem native_centered_representation (T : ℝ≥0) (X : Lp ℝ 2 P)
    (hX : AEStronglyMeasurable[usualFiltration T] (X : C(ℝ≥0, ℝ) → ℝ) P)
    (hcenter : ∫ ω, X ω ∂P = 0) :
    ∃ v : Process (E := Space Unit ℝ) usualFiltration P T,
      (HeatCanonicalNative.scalar T).integral v = X := by
  have hTH : T ≤ T + 1 := le_add_of_nonneg_right zero_le_one
  let I := HeatCanonicalNative.scalar (T + 1)
  let J := HeatTerminalItoCompression.restrictTerminal I hTH
  have hlocal := HeatTerminalItoCompression.restrictTerminal_locality I (HeatCanonicalNative.locality _) hTH
  have hcoord (i : Unit) (t : ℝ≥0) (ht : t ≤ T) :
      RawCylindricalCoordinates.value usualFiltration P T (HeatTerminalBrownian.e : Unit → Space Unit ℝ)
        J i t =ᵐ[P] (HeatCanonicalNative.family T).W i t := by
    cases i
    change I.integral (HeatTerminalItoCompression.extendIsometry hTH
      (StoppedItoInputs.stop usualFiltration P T t
        (RotatedCylindricalCoordinates.constant usualFiltration P T (HeatTerminalBrownian.e ())))) =ᵐ[P] coordinate t
    rw [HeatTerminalItoCompression.extend_stop_constant hTH ht]
    exact HeatCanonicalNative.coordinate (T + 1) t (ht.trans hTH)
  obtain ⟨v, hv⟩ := HeatTerminalItoCompression.restrictTerminal_representation I
    (HeatCanonicalNative.locality _) hTH X hX
    (native_centered_representation_later (lt_add_of_pos_right T zero_lt_one) X hX hcenter)
  exact ⟨v, (NativeIntegralUniqueness.integral (HeatCanonicalNative.family T) HeatTerminalBrownian.e
    J hlocal hcoord v).symm.trans hv⟩

/-- Canonical Hilbert-valued martingale representation for the same usual
filtration, measure and integration maps used by the stochastic heat model. -/
theorem hilbert_centered_representation {κ E : Type*} [Countable κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (T : ℝ≥0) (b : HilbertBasis κ ℝ E) (X : Lp E 2 P)
    (hX : AEStronglyMeasurable[usualFiltration T] (X : C(ℝ≥0, ℝ) → E) P)
    (hcenter : ∫ ω, X ω ∂P = 0) :
    ∃ v : Process (E := E) usualFiltration P T,
      (HeatTerminalNaturality.integral usualFiltration P T b (HeatCanonicalNative.scalar T)).integral v = X :=
  HeatHilbertMartingaleRepresentation.centered_representation usualFiltration P T b
    (HeatCanonicalNative.scalar T) (native_centered_representation T) X hX hcenter

/-- A usual-filtration terminal value has a representation of its entire
conditional-expectation process using one canonical Hilbert-valued integral. -/
theorem hilbert_conditional_representation {κ E : Type*} [Countable κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (T : ℝ≥0) (b : HilbertBasis κ ℝ E) (X : Lp E 2 P)
    (hX : AEStronglyMeasurable[usualFiltration T] (X : C(ℝ≥0, ℝ) → E) P) :
    let I := HeatTerminalNaturality.integral usualFiltration P T b (HeatCanonicalNative.scalar T)
    ∃ u : Process (E := E) usualFiltration P T,
      ∀ t : ℝ≥0, t ≤ T → P[(X : C(ℝ≥0, ℝ) → E) | usualFiltration t] =ᵐ[P]
        fun ω => (∫ z, X z ∂P) + I.integral (StoppedItoInputs.stop usualFiltration P T t u) ω :=
  HeatHilbertMartingaleRepresentation.conditional_representation usualFiltration P T
    (HeatTerminalNaturality.integral usualFiltration P T b (HeatCanonicalNative.scalar T))
    (HeatTerminalNaturality.locality usualFiltration P T b (HeatCanonicalNative.scalar T) (HeatCanonicalNative.locality T))
    (hilbert_centered_representation T b) X hX

end HeatCanonicalRightMartingaleRepresentation

#print axioms HeatCanonicalRightMartingaleRepresentation.centered_representation_later
#print axioms HeatCanonicalRightMartingaleRepresentation.native_centered_representation
#print axioms HeatCanonicalRightMartingaleRepresentation.hilbert_centered_representation
#print axioms HeatCanonicalRightMartingaleRepresentation.hilbert_conditional_representation
