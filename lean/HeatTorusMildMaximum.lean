import HeatTorusScalarMode
import HeatCoordinateEnergy
import HeatScalarMartingaleEnvelope
import HeatScalarWeakMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusMildMaximum

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusMildProjection (project)
open SHE.StoppedItoInputs HeatTorusRealCoordinates
open HeatTorusFourier (frequencySquared frequencySquared_nonneg)
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

variable {P : ℝ} {T : ℝ≥0} {M : RealState ι →L[ℝ] RealState ι}
  {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}

theorem integrable_maximum (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g)
    (Y : ℝ≥0 → Ω → RealState ι) (hYc : ∀ ω, Continuous (fun t => Y t ω))
    (hYa : StronglyAdapted F Y) (hY : ∀ t, t ≤ T → Y t =ᵐ[μ] y.value t)
    (hYu : y.process =ᵐ[energyMeasure μ T] Function.uncurry Y) :
    Integrable (fun ω => HeatPathMaximum.value T Y ω ^ 2) μ := by
  let J := HeatCanonicalNative.scalar T
  let v := HeatPredictableObservation.lift F μ T M y.process
  let q (n : Index ι) := HeatHilbertRandomStop.project F μ T (coordinate n) v
  let B := HeatCoordinateEnergy.bound coordinate T f
  have henv (n : Index ι) :
      ∃ D : Ω → ℝ, MemLp D 2 μ ∧
        (∫ ω, (D ω)^2 ∂μ) ≤ 4 * ‖q n‖^2 ∧
        ∀ᵐ ω ∂μ, ∀ t, t ≤ T → |coordinate n (Y t ω)| ≤
          2 * (|coordinate n g| + B n ω + D ω) := by
    obtain ⟨N, D, hNc, hNa, hNr, hD, hD0, hNb, hDe⟩ :=
      HeatScalarMartingaleEnvelope.exists_envelope F μ T J (HeatCanonicalNative.locality T)
        (HeatCanonicalNative.continuous_stopped T) HeatCanonicalNullComplete.contains_nulls (q n)
    refine ⟨D, hD, hDe, ?_⟩
    apply HeatScalarWeakMaximum.bound μ T (fun t ω => coordinate n (Y t ω)) N D
      (coordinate n g) (frequencySquared P n.1) (frequencySquared_nonneg P n.1)
      (fun ω => (coordinate n).continuous.comp (hYc ω)) hD0 hNb
      (coordinate n ∘ f) ((coordinate n).continuous.measurable.comp hf)
      ((coordinate n).comp_memLp' hfi)
    intro t ht
    filter_upwards [HeatTorusScalarMode.equation hf hfi hfa y Y hY hYu n t ht, hNr t] with ω h₁ h₂
    exact h₁.trans (congrArg (fun x => coordinate n g +
      (∫ r, coordinate n (f (r, ω)) ∂SHE.PredictableL2.timeMeasure t) + x) h₂.symm)
  choose D hD hDe hbound using henv
  have hsum : (∑' n : Index ι, ENNReal.ofReal (‖q n‖^2)) = ENNReal.ofReal (‖v‖^2) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := (F).predictable
    let ν := (energyMeasure μ T).trim (predictable_le_product F)
    have hnorm (n : Index ι) : ‖q n‖ = ‖((coordinate n).compLpL 2 ν) v‖ :=
      (HeatUnitHilbertLp.lpEquiv ν).norm_map _
    simp_rw [hnorm]
    exact HeatCoordinateEnergy.lp_parseval coordinate parseval ν v
  have hDf : (∑' n : Index ι, ∫⁻ ω, ENNReal.ofReal ((D n ω)^2) ∂μ) < ∞ := by
    have he (n : Index ι) : (∫⁻ ω, ENNReal.ofReal ((D n ω)^2) ∂μ) ≤
        4 * ENNReal.ofReal (‖q n‖^2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hD n).integrable_sq
        (Eventually.of_forall fun _ => sq_nonneg _)]
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal (hDe n)
    have hs := ENNReal.tsum_le_tsum he
    rw [ENNReal.tsum_mul_left, hsum] at hs
    exact hs.trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
  exact HeatCoordinateEnergy.integrable_maximum coordinate parseval μ T Y hYc
    (fun t => (hYa t).measurable.mono ((F).le t) le_rfl) g B D
    (HeatCoordinateEnergy.square_integrable coordinate μ T f hfi) hD
    (HeatCoordinateEnergy.finite coordinate parseval μ T f hf hfi) hDf hbound

end HeatTorusMildMaximum

#print axioms HeatTorusMildMaximum.integrable_maximum
