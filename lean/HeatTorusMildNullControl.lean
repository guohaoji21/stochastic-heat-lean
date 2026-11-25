import HeatTorusTerminalComparison

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace HeatTorusMildNullControl

open Filter MeasureTheory SHE SHE.PredictableL2 UnitAddTorus
open HeatTorusControlObservation (Control)
open HeatTorusFrequencyExhaustion (box box_projectLp_tendsto)
open HeatTorusGalerkinProjection (analysis project)
open HeatTorusMildTerminalControl (state state_properties terminalControl terminal_split)
open HeatTorusLiftedProjection (analyze)
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology

local notation "Ω" => C(ℝ≥0, ℝ)
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "Fle" => HeatCanonicalUsual56.usualFiltration.le
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability

private theorem adapted_pairing {H : ℝ≥0} {x : Lp Full 2 μ}
    (hx : AEStronglyMeasurable[F H] (x : Ω → Full) μ) (η : Lp Full 2 μ) :
    inner ℝ x η = inner ℝ x (condExpL2 Full ℝ (Fle H) η : Lp Full 2 μ) := by
  have h : (condExpL2 Full ℝ (Fle H) x : Lp Full 2 μ) = x := by
    apply Lp.ext
    simpa only [Lp.toLp_coeFn] using ((Lp.memLp x).condExpL2_ae_eq_condExp (𝕜 := ℝ) (Fle H)).trans
      (condExp_of_aestronglyMeasurable' (Fle H) hx ((Lp.memLp x).integrable one_le_two))
  simpa only [h] using inner_condExpL2_left_eq_right (𝕜 := ℝ) (Fle H) (f := x) (g := η)

/-- The full torus heat equation with real, analytically decaying noise
coefficient admits a predictable local null control on the canonical
completed Wiener space, uniformly bounded in the initial state. -/
theorem exists_null_control {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ)) (hb : ∀ x, (b x).im = 0)
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * HeatGevreyFourierExtension.weight k))
    {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty) {H : ℝ≥0} (hH : 0 < H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g : Full, ∃ u : Process (E := Control O) F μ H,
      ‖u‖ ≤ K * ‖g‖ ∧ state P b O H g u H = 0 := by
  obtain ⟨K, hK, hfin⟩ := HeatTorusGalerkinNullControl.exists_null_control hP hC ha b hb hdec hO hOne hH
  refine ⟨K, hK, fun g => ?_⟩
  choose u Z hZ using fun n : ℕ => hfin (box ι n) (analysis (box ι n) g)
  have hu' (n : ℕ) : ‖u n‖ ≤ K * ‖g‖ :=
    (hZ n).1.trans (mul_le_mul_of_nonneg_left (HeatTorusGalerkinProjection.analysis_contraction _ _) hK)
  let V (n : ℕ) := state P b O H g (u n) H
  let x := state P b O H g 0 H
  let A := terminalControl P b O H
  have hsplit (n : ℕ) : V n = x + A (u n) := terminal_split P b O H g (u n)
  have hV (n : ℕ) : ‖V n‖ ≤ ‖x‖ + ‖A‖ * (K * ‖g‖) := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hu' n) (norm_nonneg _))))
  have htest (η : Lp Full 2 μ) (hη : AEStronglyMeasurable[F H] (η : Ω → Full) μ) :
      Tendsto (fun n => inner ℝ (V n) η) atTop (𝓝 (0 : ℝ)) := by
    let Q (n : ℕ) := ((project (box ι n)).compLpL 2 μ) η
    let δ (n : ℕ) := HeatRegularKernel.mass (HeatTorusUniformTail.rate P n)
    let E := HeatForwardTailEnergy.energyBound H (HeatTorusGalerkinCompression.fullMultiplier b) g ((K * ‖g‖) ^ 2)
    let B := HeatTorusGalerkinTerminalDuality.noiseBound b C decay H
    have hδ n : 0 ≤ δ n := HeatRegularKernel.mass_nonneg _ (HeatTorusUniformTail.rate_pos hP n)
    have hE : 0 ≤ E := by dsimp [E, HeatForwardTailEnergy.energyBound]; positivity
    have hB : 0 ≤ B := by dsimp [B, HeatTorusGalerkinTerminalDuality.noiseBound]; positivity
    have hbound (n : ℕ) : (inner ℝ (V n) (Q n)) ^ 2 ≤
        (‖b‖ ^ 2 * (3 * δ n * E)) * (B * ‖η‖ ^ 2) := by
      change (inner ℝ (V n) (((project (box ι n)).compLpL 2 μ) η)) ^ 2 ≤ _
      rw [← HeatTorusLiftedProjection.analyze_inner]
      obtain ⟨_, _, hz₀, _, hzD, hzN, hzEnd⟩ := hZ n
      refine (HeatTorusTerminalComparison.projected_pairing_sq_le P b O H g (u n) hP hC ha hb hdec
        n (Z n) hz₀ hzD hzN hzEnd (analyze μ (box ι n) η)
          (HeatTorusLiftedProjection.analyze_adapted μ (box ι n) η hη)).trans ?_
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hu' n) 2
      have ht := pow_le_pow_left₀ (norm_nonneg _)
        (HeatTorusLiftedProjection.analyze_norm_le μ (box ι n) η) 2
      have he : HeatForwardTailEnergy.energyBound H (HeatTorusGalerkinCompression.fullMultiplier b)
          g (‖u n‖ ^ 2) ≤ E := by
        dsimp [E, HeatForwardTailEnergy.energyBound]
        gcongr
      have hmass : 0 ≤ 3 * δ n := mul_nonneg (by norm_num) (hδ n)
      gcongr
    let L := ‖b‖ ^ 2 * (3 * E) * (B * ‖η‖ ^ 2)
    have hm : Tendsto (fun n => δ n * L) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using (HeatTorusUniformTail.mass_tendsto_zero hP).mul_const L
    have hsq : Tendsto (fun n => (inner ℝ (V n) (Q n)) ^ 2) atTop (𝓝 (0 : ℝ)) :=
      squeeze_zero (fun _ => sq_nonneg _) (fun n => (hbound n).trans_eq (by dsimp [L]; ring)) hm
    have hproj : Tendsto (fun n => inner ℝ (V n) (Q n)) atTop (𝓝 (0 : ℝ)) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.norm_eq_abs, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp hsq
    have hQ : Tendsto (fun n => ‖η - Q n‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, norm_zero] using
        ((tendsto_const_nhds (x := η)).sub (box_projectLp_tendsto η)).norm
    have hd : Tendsto (fun n => inner ℝ (V n) (η - Q n)) atTop (𝓝 (0 : ℝ)) := by
      apply squeeze_zero_norm (a := fun n => (‖x‖ + ‖A‖ * (K * ‖g‖)) * ‖η - Q n‖)
      · intro n
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hV n) (norm_nonneg _))
      · simpa only [mul_zero] using hQ.const_mul (‖x‖ + ‖A‖ * (K * ‖g‖))
    have hηsum (n : ℕ) : inner ℝ (V n) (Q n) + inner ℝ (V n) (η - Q n) =
        inner ℝ (V n) η := by rw [inner_sub_right]; ring
    simpa only [hηsum, add_zero] using hproj.add hd
  have hall (η : Lp Full 2 μ) : Tendsto (fun n => inner ℝ (V n) η) atTop (𝓝 (0 : ℝ)) := by
    let η₀ := (condExpL2 Full ℝ (Fle H) η : Lp Full 2 μ)
    have h (n : ℕ) : inner ℝ (V n) η = inner ℝ (V n) η₀ := by
      obtain ⟨W, hW, he⟩ := (state_properties P b O H g (u n)).2.2.1 H
      exact adapted_pairing (hW.aestronglyMeasurable.congr he.symm) η
    simpa only [h] using htest η₀ (aestronglyMeasurable_condExpL2 (𝕜 := ℝ) (Fle H) η)
  have hweak (η : Lp Full 2 μ) :
      Tendsto (fun n => inner ℝ (A (u n)) η) atTop (𝓝 (inner ℝ (-x) η)) := by
    have he (n : ℕ) : A (u n) = V n - x := by rw [hsplit, add_comm x, add_sub_cancel_right]
    simpa only [he, inner_sub_left, zero_sub, inner_neg_left] using
      (hall η).sub_const (inner ℝ x η)
  obtain ⟨v, hv, hvn⟩ := HeatHilbertControlDuality.exists_control_of_weak_approx A (-x)
    (mul_nonneg hK (norm_nonneg _)) u hu' hweak
  exact ⟨v, hvn, by rw [terminal_split]; change x + A v = 0; rw [hv, add_neg_cancel]⟩

end HeatTorusMildNullControl

#print axioms HeatTorusMildNullControl.exists_null_control
