import HeatTorusFourierUniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusRealCoordinates

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusMildProjection (project)
open HeatTorusFourier (coefficientCLM coefficientCLM_apply frequencySquared)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local notation "Finite" => HeatTorusGalerkinBackward.State
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (Finite S) :=
  InnerProductSpace.rclikeToReal ℂ (Finite S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (Finite S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (Finite S) := ⟨rfl⟩
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "Ω" => C(ℝ≥0, ℝ)
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable

abbrev Index (ι : Type*) := (ι → ℤ) × Bool

def component (b : Bool) : ℂ →L[ℝ] ℝ := if b then Complex.reCLM else Complex.imCLM

def coordinate (n : Index ι) : RealState ι →L[ℝ] ℝ :=
  (component n.2).comp ((coefficientCLM n.1).comp embed)

theorem parseval (v : RealState ι) :
    (∑' n : Index ι, ENNReal.ofReal ((coordinate n v)^2)) =
      ENNReal.ofReal (‖v‖^2) := by
  have hp := hasSum_sq_mFourierCoeff (embed v)
  have hpair (k : ι → ℤ) : (∑' b : Bool, ENNReal.ofReal ((coordinate (k,b) v)^2)) =
      ENNReal.ofReal (‖mFourierCoeff (embed v) k‖^2) := by
    rw [tsum_fintype, Fintype.sum_bool]
    simp only [coordinate, ContinuousLinearMap.comp_apply, component, Bool.false_eq_true,
      if_false, if_true, Complex.imCLM_apply, Complex.reCLM_apply, coefficientCLM_apply]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    ring_nf
  rw [ENNReal.tsum_prod']
  simp_rw [hpair]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hp.summable, hp.tsum_eq,
    ← realLp_norm_sq, HeatTorusFourierUniqueness.embed_norm]

end HeatTorusRealCoordinates

#print axioms HeatTorusRealCoordinates.parseval
