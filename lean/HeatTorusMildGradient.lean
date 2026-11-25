import HeatTorusProjectedEnergy
import HeatTorusGradientProcess

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace HeatTorusMildGradient

open Filter MeasureTheory SHE SHE.PredictableL2 UnitAddTorus HeatTorusReal
open HeatTorusFourier (frequencySquared frequencySquared_nonneg)
open HeatTorusSobolevFourier (modeEnergy modeEnergy_nonneg)
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
local instance : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "Ω" => C(ℝ≥0, ℝ)
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable

private theorem project_norm (S : Finset (ι → ℤ)) :
    ‖HeatTorusMildProjection.project S‖ ≤ ‖(embed : RealState ι →L[ℝ] Full)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (HeatTorusGalerkinProjection.analysis_contraction S (embed x)).trans
    ((embed : RealState ι →L[ℝ] Full).le_opNorm x)

private theorem lp_norm_bound {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : E →L[ℝ] G) (x : Lp E 2 μ) :
    ‖(A.compLpL 2 μ) x‖ ≤ ‖A‖ * ‖x‖ :=
  ((A.compLpL 2 μ).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (A.norm_compLpL_le) (norm_nonneg _))

private theorem spatial_nonneg (S : Finset (ι → ℤ)) (P : ℝ) (x : Finite S) :
    0 ≤ HeatTorusProjectedEnergy.spatial S P x :=
  Finset.sum_nonneg fun k _ => mul_nonneg (frequencySquared_nonneg P k.val) (sq_nonneg _)

private theorem spatial_integrable {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {S : Finset (ι → ℤ)} (P : ℝ) {x : α → Finite S} (hx : MemLp x 2 ν) :
    Integrable (fun a => HeatTorusProjectedEnergy.spatial S P (x a)) ν := by
  apply integrable_finsetSum
  intro k _
  let A : Finite S →L[ℂ] ℂ := PiLp.proj 2 _ k
  have hk := A.lipschitzWith.comp_memLp (map_zero A) hx
  exact hk.norm.integrable_sq.const_mul _

/-- The paper's actual canonical mild solution has square-integrable spatial
weak gradients on every finite time interval. -/
theorem exists_gradient {P : ℝ} {T : ℝ≥0}
    {M : RealState ι →L[ℝ] RealState ι} {f : ℝ≥0 × Ω → RealState ι}
    (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω))) {g : RealState ι}
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g) :
    ∃ D : ι → (ℝ≥0 × Ω) → Full, (∀ i, StronglyMeasurable[(F).predictable] (D i)) ∧
      (∀ i, MemLp (D i) 2 (energyMeasure μ T)) ∧
      ∀ᵐ p ∂energyMeasure μ T, HeatTorusGradient.HasGradient P (embed (y.process p)) (fun i => D i p) := by
  classical
  let e : RealState ι →L[ℝ] Full := embed
  let C := ‖e‖
  let ν := energyMeasure μ T
  let τ := timeMeasure T
  let v := y.value
  have hv := HeatPredictableObservation.ambient_memLp F μ T y.process
  have hvs : MemLp v 2 τ := by
    obtain ⟨K, hK, hk⟩ := HeatCompactLpBound.exists_bound μ T v y.continuous_value
    apply (memLp_const K).mono' y.continuous_value.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem T] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg hK] using hk t ht.2
  let B := (C * ‖Lp.const 2 μ g‖) ^ 2 + (∫ p, (C * ‖f p‖) ^ 2 ∂ν) +
    (∫ t, (C * ‖v t‖) ^ 2 ∂τ) + ∫ t, (C * ‖M‖ * ‖v t‖) ^ 2 ∂τ
  have hambient (S : Finset (ι → ℤ)) :
      (∫⁻ p, ∑ k ∈ S, ENNReal.ofReal (modeEnergy P ((e ∘ y.process) p) k) ∂ν) ≤ ENNReal.ofReal B := by
    let A := HeatTorusMildProjection.project S
    let q := HeatTimeLpField.value μ (A ∘ f)
    have hAf := A.lipschitzWith.comp_memLp (map_zero A) hfi
    have hqm := A.continuous.measurable.comp hf
    have hq := HeatTimeLpField.square_integrable μ (A ∘ f) hqm T hAf
    obtain ⟨X, hX, hd, hn⟩ := HeatTorusMildProjection.projected_trajectory S hf hfi hfa y
    have hXb := HeatTorusProjectedEnergy.bound
      (HeatTerminalNaturality.locality F μ T _ _ (HeatCanonicalNative.locality T)) X q hq
      (Eventually.of_forall hd)
    have hstate (t : ℝ≥0) : ‖X.state t‖ ≤ C * ‖v t‖ := by
      rw [hX t]
      exact (lp_norm_bound A (v t)).trans
        (mul_le_mul_of_nonneg_right (project_norm S) (norm_nonneg _))
    have hnoise : ∀ᵐ t ∂τ, ‖X.noise t‖ ≤ C * ‖M‖ * ‖v t‖ := by
      filter_upwards [hn] with t ht
      rw [ht]
      refine (lp_norm_bound (A.comp M) (v t)).trans ?_
      exact mul_le_mul_of_nonneg_right ((A.opNorm_comp_le M).trans
        (mul_le_mul_of_nonneg_right (project_norm S) (norm_nonneg _))) (norm_nonneg _)
    have hfbound (p : ℝ≥0 × Ω) : ‖A (f p)‖ ≤ C * ‖f p‖ :=
      (A.le_opNorm (f p)).trans (mul_le_mul_of_nonneg_right (project_norm S) (norm_nonneg _))
    have hF : (∫ t, ‖q t‖ ^ 2 ∂τ) ≤ ∫ p, (C * ‖f p‖) ^ 2 ∂ν := by
      rw [HeatTimeLpField.energy μ (A ∘ f) hqm T hAf]
      apply integral_mono hAf.norm.integrable_sq
      · simpa only [mul_pow] using hfi.norm.integrable_sq.const_mul (C ^ 2)
      · intro p
        exact pow_le_pow_left₀ (norm_nonneg _) (hfbound p) 2
    have hV : (∫ t, ‖X.state t‖ ^ 2 ∂τ) ≤ ∫ t, (C * ‖v t‖) ^ 2 ∂τ := by
      apply integral_mono X.state_square.norm.integrable_sq
      · simpa only [mul_pow] using hvs.norm.integrable_sq.const_mul (C ^ 2)
      · intro t
        exact pow_le_pow_left₀ (norm_nonneg _) (hstate t) 2
    have hN : (∫ t, ‖X.noise t‖ ^ 2 ∂τ) ≤ ∫ t, (C * ‖M‖ * ‖v t‖) ^ 2 ∂τ := by
      apply integral_mono_ae X.noise_square.norm.integrable_sq
      · simpa only [mul_pow] using hvs.norm.integrable_sq.const_mul (C ^ 2 * ‖M‖ ^ 2)
      · filter_upwards [hnoise] with t ht
        exact pow_le_pow_left₀ (norm_nonneg _) ht 2
    have h0 : ‖X.state 0‖ ^ 2 ≤ (C * ‖Lp.const 2 μ g‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      rw [← y.initial_value]
      exact hstate 0
    rw [integral_add hq.norm.integrable_sq X.state_square.norm.integrable_sq] at hXb
    let d (p : ℝ≥0 × Ω) := HeatTorusProjectedEnergy.spatial S P (A (y.process p))
    have hdi : Integrable d ν := spatial_integrable P
      (A.lipschitzWith.comp_memLp (map_zero A) hv)
    have hd0 (p : ℝ≥0 × Ω) : 0 ≤ d p := spatial_nonneg S P _
    have hds : (∫ p, d p ∂ν) = ∫ t, ∫ ω, HeatTorusProjectedEnergy.spatial S P (X.state t ω) ∂μ ∂τ := by
      change (∫ p, d p ∂(timeMeasure T).prod μ) = _
      rw [integral_prod _ hdi]
      apply integral_congr_ae
      filter_upwards [y.slices] with t ht
      rw [hX t]
      apply integral_congr_ae
      filter_upwards [ht, A.coeFn_compLpL (y.value t)] with ω h₁ h₂
      change HeatTorusProjectedEnergy.spatial S P (A (y.process (t, ω))) =
        HeatTorusProjectedEnergy.spatial S P (((A.compLpL 2 μ) (y.value t)) ω)
      rw [h₂, h₁]
    rw [← hds] at hXb
    have hB : (∫ p, d p ∂ν) ≤ B := by
      have hp : 0 ≤ ∫ p, d p ∂ν := integral_nonneg (show 0 ≤ d from hd0)
      dsimp only [B]
      linarith only [hXb, hF, hV, hN, h0, hp]
    have hdMode (p : ℝ≥0 × Ω) : d p = ∑ k ∈ S, modeEnergy P (e (y.process p)) k := by
      change (∑ k : ↥S, frequencySquared P k.val *
        ‖HeatTorusGalerkinProjection.analysis S (e (y.process p)) k‖ ^ 2) = _
      simp only [HeatTorusGalerkinProjection.analysis_apply]
      exact Finset.sum_coe_sort S (fun k => modeEnergy P (e (y.process p)) k)
    calc
      (∫⁻ p, ∑ k ∈ S, ENNReal.ofReal (modeEnergy P ((e ∘ y.process) p) k) ∂ν) =
          ∫⁻ p, ENNReal.ofReal (d p) ∂ν := by
        congr with p
        rw [hdMode, ENNReal.ofReal_sum_of_nonneg (fun k _ => modeEnergy_nonneg P _ k)]
        rfl
      _ = ENNReal.ofReal (∫ p, d p ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hdi (Eventually.of_forall hd0)).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hB
  let νp := ν.trim (predictable_le_product F)
  have hm : Measurable[(F).predictable] (e ∘ y.process) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := (F).predictable
    exact e.continuous.measurable.comp (Lp.stronglyMeasurable y.process).measurable
  have hgrad :
      ∃ D : ι → (ℝ≥0 × Ω) → Full, (∀ i, MemLp (D i) 2 νp) ∧
        ∀ᵐ p ∂νp, HeatTorusGradient.HasGradient P (e (y.process p)) (fun i => D i p) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := (F).predictable
    apply HeatTorusGradientProcess.exists_gradient P νp (e ∘ y.process) hm
      (ENNReal.ofReal B) ENNReal.ofReal_lt_top
    intro S
    have hs : Measurable[(F).predictable] (fun p => ∑ k ∈ S,
        ENNReal.ofReal (modeEnergy P ((e ∘ y.process) p) k)) := by
      apply Finset.measurable_sum
      intro k _
      have hc : Measurable[(F).predictable] (fun p => mFourierCoeff (e (y.process p)) k) := by
        have he : (fun p => mFourierCoeff (e (y.process p)) k) =
            (HeatTorusFourier.coefficientCLM k) ∘ e ∘ y.process :=
          funext fun p => (HeatTorusFourier.coefficientCLM_apply k (e (y.process p))).symm
        rw [he]
        exact (HeatTorusFourier.coefficientCLM k).continuous.measurable.comp hm
      exact (measurable_const.mul (hc.norm.pow_const 2)).ennreal_ofReal
    rw [lintegral_trim (predictable_le_product F) hs]
    exact hambient S
  obtain ⟨D, hDi, hD⟩ := hgrad
  let D' (i : ι) := (hDi i).aestronglyMeasurable.mk (D i)
  have hDe (i : ι) : D i =ᵐ[νp] D' i := (hDi i).aestronglyMeasurable.ae_eq_mk
  refine ⟨D', fun i => (hDi i).aestronglyMeasurable.stronglyMeasurable_mk, fun i => ?_, ?_⟩
  · exact memLp_of_memLp_trim (predictable_le_product F) ((memLp_congr_ae (hDe i)).mp (hDi i))
  · apply ae_of_ae_trim (predictable_le_product F)
    filter_upwards [hD, ae_all_iff.mpr hDe] with p hp he
    simpa only [← he] using hp

end HeatTorusMildGradient

#print axioms HeatTorusMildGradient.exists_gradient
