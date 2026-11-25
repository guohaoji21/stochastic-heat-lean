import HeatTorusVariationalOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace HeatTorusVariationalForm

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusMildProjection (project)
open SHE.StoppedItoInputs
open scoped NNReal ENNReal Topology

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

local instance : InnerProductSpace ℝ Full := InnerProductSpace.rclikeToReal ℂ Full

variable {P : ℝ} {T : ℝ≥0} {M : RealState ι →L[ℝ] RealState ι}
  {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}

theorem finite_gradient_form (t : ℝ≥0) (ht : t ≤ T) (S : Finset (ι → ℤ))
    (z : Finite S) (E : ι → Full)
    (hE : HeatTorusGradient.HasGradient P (HeatTorusGalerkinProjection.synthesis S z) E)
    (u : Process (E := RealState ι) F μ T) (V : ℝ≥0 → Lp (RealState ι) 2 μ)
    (hc : Continuous V)
    (hu : ∀ᵐ r ∂timeMeasure T, (fun ω => u (r, ω)) =ᵐ[μ] V r)
    (D : ι → (ℝ≥0 × Ω) → Full) (hDm : ∀ i, Measurable (D i))
    (hDi : ∀ i, MemLp (D i) 2 (energyMeasure μ T))
    (hD : ∀ᵐ p ∂energyMeasure μ T, HeatTorusGradient.HasGradient P (embed (u p)) (fun i => D i p)) :
    ((innerSL ℝ z).compLpL 2 μ)
      (∫ r, ((HeatTorusGalerkinBackward.laplace S P).compLpL 2 μ)
        (((project S).compLpL 2 μ) (V r)) ∂timeMeasure t) =
      -∑ i, fullPair (E i) (∫ r, HeatTimeLpField.value μ (D i) r ∂timeMeasure t) := by
  classical
  let A := project S
  let L := HeatTorusGalerkinBackward.laplace S P
  let C := (innerSL ℝ z).compLpL 2 μ
  let Q (i : ι) := (innerSL ℝ (E i)).compLpL 2 μ
  let x (r : ℝ≥0) := (L.compLpL 2 μ) ((A.compLpL 2 μ) (V r))
  let B (i : ι) (r : ℝ≥0) := HeatTimeLpField.value μ (D i) r
  have hxc : Continuous x := (L.compLpL 2 μ).continuous.comp ((A.compLpL 2 μ).continuous.comp hc)
  have hxi : Integrable x (timeMeasure t) := by
    obtain ⟨K, hK, h⟩ := HeatCompactLpBound.exists_bound μ t x hxc
    apply (integrable_const K).mono' hxc.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem t] with q hq
    exact h q hq.2
  have hDit (i : ι) := (hDi i).mono_measure (Measure.prod_mono (HeatTimeRestriction.mono ht) le_rfl)
  have hBi (i : ι) : Integrable (B i) (timeMeasure t) :=
    (HeatTimeLpField.square_integrable μ (D i) (hDm i) t (hDit i)).integrable one_le_two
  have hB : ∀ᵐ r ∂timeMeasure t, ∀ i, (B i r : Ω → Full) =ᵐ[μ] fun ω => D i (r,ω) :=
    ae_all_iff.mpr (fun i => HeatTimeLpField.value_ae μ (D i) (hDm i) t (hDit i))
  have hp : ∀ᵐ r ∂timeMeasure t, ∀ᵐ ω ∂μ,
      HeatTorusGradient.HasGradient P (embed (u (r,ω))) (fun i => D i (r,ω)) :=
    ae_mono (HeatTimeRestriction.mono ht) (Measure.ae_ae_of_ae_prod hD)
  have hX : ∀ᵐ r ∂timeMeasure t,
      C (x r) = -∑ i, Q i (B i r) := by
    filter_upwards [hp, hB, ae_mono (HeatTimeRestriction.mono ht) hu] with r hr hB hrU
    apply Lp.ext
    have hq : ∀ᵐ ω ∂μ, ∀ i, Q i (B i r) ω = (innerSL ℝ (E i)) (B i r ω) :=
      ae_all_iff.mpr (fun i => (innerSL ℝ (E i)).coeFn_compLpL (B i r))
    have hbr : ∀ᵐ ω ∂μ, ∀ i, B i r ω = D i (r,ω) := ae_all_iff.mpr hB
    filter_upwards [hr, hrU, (innerSL ℝ z).coeFn_compLpL (x r),
      L.coeFn_compLpL ((A.compLpL 2 μ) (V r)), A.coeFn_compLpL (V r), hq, hbr,
      Lp.coeFn_neg (∑ i, Q i (B i r)), Lp.coeFn_finsetSum Finset.univ (fun i => Q i (B i r))]
      with ω hDω hU hC hL hA hQ hB hneg hsum
    change C (x r) ω = (-∑ i, Q i (B i r)) ω
    change C (x r) ω = (innerSL ℝ z) (x r ω) at hC
    change x r ω = L (((A.compLpL 2 μ) (V r)) ω) at hL
    rw [hC, innerSL_apply_apply, hL, hA, ← hU, hneg, Pi.neg_apply, hsum]
    simp only [Finset.sum_apply]
    change (inner ℂ z (L (HeatTorusGalerkinProjection.analysis S (embed (u (r,ω)))))).re =
      -∑ i, (Q i (B i r) ω)
    simp_rw [hQ, hB]
    have h := congrArg Complex.reCLM (HeatTorusSpectralForm.weak_form P S z (embed (u (r,ω)))
      (fun i => D i (r,ω)) E hDω hE)
    simp only [innerSL_apply_apply]
    change (inner ℂ z (L (HeatTorusGalerkinProjection.analysis S (embed (u (r,ω)))))).re =
      -∑ i, (inner ℂ (E i) (D i (r,ω))).re
    simpa only [map_neg, map_sum, Complex.reCLM_apply, L] using h
  change C (∫ r, x r ∂timeMeasure t) = -∑ i, Q i (∫ r, B i r ∂timeMeasure t)
  rw [← C.integral_comp_comm hxi, integral_congr_ae hX, integral_neg]
  rw [integral_finsetSum _ (fun i _ => (Q i).integrable_comp (hBi i))]
  simp_rw [ContinuousLinearMap.integral_comp_comm _ (hBi _)]

end HeatTorusVariationalForm

#print axioms HeatTorusVariationalForm.finite_gradient_form
