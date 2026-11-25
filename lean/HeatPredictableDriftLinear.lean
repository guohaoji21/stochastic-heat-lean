import HeatPredictableDriftCell

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace HeatPredictableDriftLinear

open Filter MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

theorem drift_add (a b : ℝ≥0) (f g : Process (E := E) F μ H) :
    HeatPredictableDriftCell.value a b (f + g) =
      HeatPredictableDriftCell.value a b f + HeatPredictableDriftCell.value a b g := by
  have h := HeatPredictableDriftCell.sub a b (f + g) g
  rw [add_sub_cancel_right] at h
  exact (sub_eq_iff_eq_add.mp h.symm)

theorem drift_smul (a b : ℝ≥0) (c : ℝ) (f : Process (E := E) F μ H) :
    HeatPredictableDriftCell.value a b (c • f) = c • HeatPredictableDriftCell.value a b f := by
  have he : ((c • f : Process F μ H) : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] c • (f : ℝ≥0 × Ω → E) :=
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul c f)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  apply Lp.ext
  filter_upwards [HeatPredictableDriftCell.value_ae a b (c • f), HeatPredictableDriftCell.value_ae a b f,
    Lp.coeFn_smul c (HeatPredictableDriftCell.value a b f),
    Measure.ae_ae_of_ae_prod hs]
    with ω hl hf hsm hfs
  rw [hl, hsm]
  simp only [Pi.smul_apply, hf, HeatBochnerCell.value]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_mono Measure.restrict_le_self hfs] with t ht
  exact ht


/-- Time integration on the full predictable horizon is a bounded linear map. -/
def integral (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    Process (E := E) F μ H →L[ℝ] Lp E 2 μ :=
  (show Process (E := E) F μ H →ₗ[ℝ] Lp E 2 μ from
    { toFun := HeatPredictableDriftCell.value 0 H
      map_add' := drift_add 0 H
      map_smul' := drift_smul 0 H }).mkContinuous (Real.sqrt (H : ℝ)) fun f => by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    have hs : (Real.sqrt (H : ℝ)) ^ 2 = (H : ℝ) := Real.sq_sqrt H.property
    rw [mul_pow, hs]
    change ‖HeatPredictableDriftCell.value 0 H f‖ ^ 2 ≤ (H : ℝ) * ‖f‖ ^ 2
    simpa only [NNReal.coe_zero, sub_zero] using
      HeatPredictableDriftCell.norm_sq_le (show 0 ≤ H from bot_le) le_rfl f

end HeatPredictableDriftLinear

#print axioms HeatPredictableDriftLinear.integral
