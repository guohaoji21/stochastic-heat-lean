import HeatTorusGalerkinProjection
import HeatTerminalCrossNaturality
import HeatVolterraSlice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1550000
noncomputable section

namespace HeatTorusProjectedConvolution

open Filter MeasureTheory UnitAddTorus SHE SHE.PredictableL2 SHE.HilbertColumns
open HeatTorusGalerkinProjection (analysis synthesis)
open HeatTorusGalerkinBackward (State)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)

def fullHeat (P : ℝ) (t : ℝ≥0) : Full →L[ℝ] Full := (HeatTorusFourier.heat P t).restrictScalars ℝ

theorem fullHeat_continuous (P : ℝ) (x : Full) : Continuous (fun t : ℝ≥0 => fullHeat P t x) :=
  (HeatTorusFourier.continuous_heat P x).comp continuous_subtype_val

theorem fullHeat_contraction (P : ℝ) (t : ℝ≥0) (x : Full) : ‖fullHeat P t x‖ ≤ ‖x‖ :=
  HeatTorusFourier.contraction P t x

def finiteHeat (S : Finset (ι → ℤ)) (P : ℝ) (t : ℝ≥0) : State S →L[ℝ] State S :=
  ((analysis S).restrictScalars ℝ).comp ((fullHeat P t).comp ((synthesis S).restrictScalars ℝ))

theorem finiteHeat_apply (S : Finset (ι → ℤ)) (P : ℝ) (t : ℝ≥0) (x : State S) (k : ↥S) :
    finiteHeat S P t x k = HeatTorusFourier.multiplier P t k.val * x k := by
  classical
  change analysis S (HeatTorusFourier.heat P t (synthesis S x)) k = _
  rw [HeatTorusGalerkinProjection.analysis_apply, HeatTorusFourier.fourierCoeff_heat,
    HeatTorusGalerkinProjection.coefficient_synthesis, dite_eq_left k.property]

theorem analysis_heat (S : Finset (ι → ℤ)) (P : ℝ) (t : ℝ≥0) (x : Full) :
    analysis S (fullHeat P t x) = finiteHeat S P t (analysis S x) := by
  ext k
  change analysis S (HeatTorusFourier.heat P t x) k = finiteHeat S P t (analysis S x) k
  rw [HeatTorusGalerkinProjection.analysis_apply, HeatTorusFourier.fourierCoeff_heat, finiteHeat_apply,
    HeatTorusGalerkinProjection.analysis_apply]

theorem finiteHeat_continuous (S : Finset (ι → ℤ)) (P : ℝ) (x : State S) :
    Continuous (fun t : ℝ≥0 => finiteHeat S P t x) :=
  (analysis S).continuous.comp (fullHeat_continuous P (synthesis S x))

theorem finiteHeat_contraction (S : Finset (ι → ℤ)) (P : ℝ) (t : ℝ≥0) (x : State S) :
    ‖finiteHeat S P t x‖ ≤ ‖x‖ := by
  change ‖analysis S (fullHeat P t (synthesis S x))‖ ≤ _
  exact (HeatTorusGalerkinProjection.analysis_contraction _ _).trans
    ((fullHeat_contraction _ _ _).trans_eq (HeatTorusGalerkinProjection.synthesis_norm _ _))

section Convolution

local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

variable {Ω κ ℓ : Type*} [mΩ : MeasurableSpace Ω] [Countable κ] [Countable ℓ]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

local notation "ν" => Measure.trim (energyMeasure μ H) (predictable_le_product F)

/-- Projecting the full heat convolution integrand gives the finite heat
convolution applied to the projected full diffusion. -/
theorem slice_eq (S : Finset (ι → ℤ)) (P : ℝ) (M : Full →L[ℝ] Full)
    (t : ℝ≥0) (u : Process (E := Full) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    let A := (analysis S).restrictScalars ℝ
    (A.compLpL 2 ν) (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P)
      (fullHeat_contraction P) M t u) =
      HeatVolterraSlice.slice F μ H (finiteHeat S P) (finiteHeat_continuous S P)
        (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) t (((A.comp M).compLpL 2 ν) u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let A := (analysis S).restrictScalars ℝ
  let v := ((A.comp M).compLpL 2 ν) u
  let w := HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P) M t u
  let z := HeatVolterraSlice.slice F μ H (finiteHeat S P) (finiteHeat_continuous S P)
    (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) t v
  change (A.compLpL 2 ν) w = z
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim (A.coeFn_compLpL w), ae_eq_of_ae_eq_trim ((A.comp M).coeFn_compLpL u),
    HeatVolterraSlice.slice_ae F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P) M t u,
    HeatVolterraSlice.slice_ae F μ H (finiteHeat S P) (finiteHeat_continuous S P)
      (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) t v] with p hw hv hf hz
  change (A.compLpL 2 ν) w p = z p
  rw [hw, hf, hz]
  unfold HeatVolterraKernel.raw
  by_cases ht : p.1 < t
  · simp only [ite_eq_left ht, ContinuousLinearMap.id_apply]
    change v p = A (M (u p)) at hv
    rw [hv]
    exact analysis_heat S P (t - p.1) (M (u p))
  · simp only [ite_eq_right ht, map_zero]

/-- The stochastic convolution itself commutes with Fourier analysis when
the full and finite Hilbert integrals use the same scalar Brownian motion. -/
theorem convolution_eq (S : Finset (ι → ℤ)) (P : ℝ) (M : Full →L[ℝ] Full)
    (b : HilbertBasis κ ℝ Full) (c : HilbertBasis ℓ ℝ (State S))
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (t : ℝ≥0) (u : Process (E := Full) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    let A := (analysis S).restrictScalars ℝ
    (A.compLpL 2 μ) ((HeatTerminalNaturality.integral F μ H b J).integral
      (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P) M t u)) =
      (HeatTerminalNaturality.integral F μ H c J).integral
        (HeatVolterraSlice.slice F μ H (finiteHeat S P) (finiteHeat_continuous S P)
          (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) t (((A.comp M).compLpL 2 ν) u)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  intro A
  rw [HeatTerminalCrossNaturality.commutes F μ H b c J A, slice_eq F μ H S P M t u]

end Convolution

end HeatTorusProjectedConvolution

#print axioms HeatTorusProjectedConvolution.analysis_heat
#print axioms HeatTorusProjectedConvolution.convolution_eq
