import HeatBackwardDriver
import HeatProgressiveControl
import HeatVolterraFixedPoint
import HeatVolterraContinuity
import HeatPredictableGate
import SHE.RotatedCylindricalCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace HeatBackwardDriverProcess

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open HeatBackwardDriver (state terminal mean)
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

private abbrev identity (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ℝ≥0 → E →L[ℝ] E := fun _ => ContinuousLinearMap.id ℝ E

private theorem gate_measurable (a b : ℝ≥0) :
    MeasurableSet[F.predictable] (Prod.fst ⁻¹' Ioc a b) :=
  measurableSet_Ioc.preimage (PredictableClock.time_measurable F)

private theorem exists_drift_process (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (a : ℝ≥0) (f : Process (E := E) F μ H) :
    ∃ v : Process (E := E) F μ H, ∀ᵐ t ∂timeMeasure H, a ≤ t →
      (fun ω => v (t, ω)) =ᵐ[μ] HeatPredictableDriftCell.value a t f := by
  let u := post F μ H a f
  let U := Function.curry (u : ℝ≥0 × Ω → E)
  have hU : IsStronglyPredictable F U := Lp.stronglyMeasurable u
  have hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  obtain ⟨v, X, _, _, _, hv, hX, _⟩ := HeatProgressiveControl.exists_version F μ H
    (identity E) (fun _ => continuous_const) (fun _ _ => le_rfl)
    hnull U hU.isStronglyProgressive hE
  have hpost := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (post_ae F μ H a f)
  have hraw (t : ℝ≥0) :
      HeatControlConvolution.value H (identity E) (HeatControlAdapted.clamp U H) t =ᵐ[μ]
        HeatBochnerCell.value H f a t := by
    filter_upwards [Measure.ae_ae_of_ae_prod hpost] with ω hw
    unfold HeatControlConvolution.value HeatBochnerCell.value
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [hw, timeMeasure_ae_mem H, (timeMeasure H).ae_ne t] with s hu hs hne
    simp only [HeatControlConvolution.raw, HeatVolterraKernel.raw, HeatControlAdapted.clamp,
      min_eq_left hs.2, identity, ContinuousLinearMap.id_apply, U, Function.curry_apply, u]
    change u (s, ω) = (if a < s then f (s, ω) else 0) at hu
    by_cases hst : s < t
    · rw [if_pos hst, hu]
      by_cases has : a < s
      · rw [if_pos has, indicator_of_mem (show s ∈ Ioc a t from ⟨has, hst.le⟩)]
      · rw [if_neg has, indicator_of_notMem (show s ∉ Ioc a t from fun h => has h.1)]
    · rw [if_neg hst, indicator_of_notMem (show s ∉ Ioc a t from
        fun h => hne (le_antisymm h.2 (le_of_not_gt hst)))]
  refine ⟨v, ?_⟩
  have hv' : ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] X t :=
    Measure.ae_ae_of_ae_prod hv
  filter_upwards [hv'] with t ht
  intro _
  exact ht.trans ((hX t).trans ((hraw t).trans (HeatPredictableDriftCell.value_ae a t f).symm))

private theorem exists_stopped_process (J : StandardTerminalIto (C := E) (E := E) F μ H)
    (u : Process (E := E) F μ H) :
    ∃ v : Process (E := E) F μ H, ∀ᵐ t ∂timeMeasure H,
      (fun ω => v (t, ω)) =ᵐ[μ] J.integral (stop F μ H t u) := by
  let S := identity E
  have hS (x : E) : Continuous (fun t => S t x) := continuous_const
  have hc (t : ℝ≥0) (x : E) : ‖S t x‖ ≤ ‖x‖ := le_rfl
  have hm (s t : ℝ≥0) : S (s + t) = (S s).comp (S t) := (ContinuousLinearMap.id_comp _).symm
  have hs (t : ℝ≥0) : HeatVolterraSlice.slice F μ H S hS hc (ContinuousLinearMap.id ℝ E) t u =
      stop F μ H t u := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [HeatVolterraSlice.slice_ae F μ H S hS hc (ContinuousLinearMap.id ℝ E) t u,
      stop_ae F μ H t u] with p hsl hstop
    rw [hsl, hstop]
    by_cases hp : p.1 < t
    · rw [Set.indicator_of_mem (show p ∈ before (t : ℝ) from hp)]
      simp only [HeatVolterraKernel.raw, if_pos hp, S, identity, ContinuousLinearMap.id_apply]
    · rw [Set.indicator_of_notMem (show p ∉ before (t : ℝ) from hp)]
      simp only [HeatVolterraKernel.raw, if_neg hp]
  refine ⟨HeatVolterraFixedPoint.convolution F μ H S hS hc (ContinuousLinearMap.id ℝ E) hm J u, ?_⟩
  filter_upwards [HeatVolterraContinuity.convolution_slices F μ H S hS hc
    (ContinuousLinearMap.id ℝ E) J hm u] with t ht
  simpa only [HeatVolterraFixedPoint.convolution, hs] using ht

/-- The prescribed state represented by one predictable L² process supported
on the current cell, on the original filtration and time-probability measure. -/
def Realizes (a b : ℝ≥0) (η : Lp E 2 μ) (f v : Process (E := E) F μ H) : Prop :=
  ∀ᵐ t ∂timeMeasure H,
    ((fun ω => v (t, ω)) =ᵐ[μ] (Ioc a b).indicator (fun t => (state b η f t : Ω → E)) t)

theorem exists_state_process (J : StandardTerminalIto (C := E) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    {a b : ℝ≥0} (hb : b ≤ H) (η : Lp E 2 μ) (f u : Process (E := E) F μ H)
    (hu : J.integral u = terminal a b η f - mean (terminal a b η f)) :
    ∃ v : Process (E := E) F μ H, Realizes a b η f v := by
  obtain ⟨d, hd⟩ := exists_drift_process hnull a f
  obtain ⟨w, hw⟩ := exists_stopped_process J u
  let c := ∫ ω, terminal a b η f ω ∂μ
  let C := RotatedCylindricalCoordinates.constant F μ H c
  let B : Set (ℝ≥0 × Ω) := Prod.fst ⁻¹' Ioc a b
  let v := HeatPredictableGate.gate F μ H B (gate_measurable a b) (C + w - d)
  refine ⟨v, ?_⟩
  have hgate := Measure.ae_ae_of_ae_prod (HeatPredictableGate.gate_ae F μ H B
    (gate_measurable a b) (C + w - d))
  have hconst := Measure.ae_ae_of_ae_prod (RotatedCylindricalCoordinates.constant_ae F μ H c)
  have hadd := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_add C w))
  have hsub := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub (C + w) d))
  unfold Realizes
  filter_upwards [hd, hw, hgate, hconst, hadd, hsub] with t ht hw hg hc ha hs
  by_cases h : t ∈ Ioc a b
  · rw [indicator_of_mem h, HeatBackwardDriver.state_eq_stopped J hJ h.1.le h.2 hb η f u hu]
    filter_upwards [ht h.1.le, hw, hg, hc, ha, hs,
      Lp.coeFn_const 2 μ c,
      Lp.coeFn_add (mean (terminal a b η f)) (J.integral (stop F μ H t u)),
      Lp.coeFn_sub (mean (terminal a b η f) + J.integral (stop F μ H t u))
        (HeatPredictableDriftCell.value a t f)] with ω hd hw hg hc ha hs hc' ha' hs'
    change v (t, ω) = _
    rw [hg, indicator_of_mem (show (t, ω) ∈ B from h), hs, Pi.sub_apply, ha, Pi.add_apply,
      hc, hw, hd, hs', Pi.sub_apply, ha', Pi.add_apply]
    exact congrArg (fun x => x + J.integral (stop F μ H t u) ω - HeatPredictableDriftCell.value a t f ω)
      hc'.symm
  · rw [indicator_of_notMem h]
    filter_upwards [hg] with ω hg
    change v (t, ω) = 0
    rw [hg, indicator_of_notMem (show (t, ω) ∉ B from h)]

/-- Integrated L² stability of the actual predictable state on a short cell. -/
theorem norm_sq_sub_le {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H) (η : Lp E 2 μ)
    (f g v w : Process (E := E) F μ H) (hv : Realizes a b η f v) (hw : Realizes a b η g w) :
    ‖v - w‖ ^ 2 ≤ ((b : ℝ) - a) ^ 2 * ‖f - g‖ ^ 2 := by
  let C := ((b : ℝ) - a) * ‖f - g‖ ^ 2
  let bound := (Ioc a b).indicator (fun _ => C)
  have hC : 0 ≤ C := mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hab)) (sq_nonneg _)
  have hbound : Integrable bound (timeMeasure H) := (integrable_const C).indicator measurableSet_Ioc
  have hi := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp (v - w))).norm.integrable_sq
  rw [process_integral_energy]
  have hle : (∫ t, ∫ ω, ‖(v - w) (t, ω)‖ ^ 2 ∂μ ∂timeMeasure H) ≤
      ∫ t, bound t ∂timeMeasure H := by
    apply integral_mono_ae hi.integral_prod_left hbound
    filter_upwards [hv, hw, Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub v w))]
      with t hv hw hs
    by_cases ht : t ∈ Ioc a b
    · rw [show bound t = C from indicator_of_mem ht _]
      rw [indicator_of_mem ht] at hv hw
      have he : (∫ ω, ‖(v - w) (t, ω)‖ ^ 2 ∂μ) = ‖state b η f t - state b η g t‖ ^ 2 := by
        rw [realLp_norm_sq]
        apply integral_congr_ae
        filter_upwards [hv, hw, hs, Lp.coeFn_sub (state b η f t) (state b η g t)] with ω hv hw hs hd
        rw [hs, Pi.sub_apply, hv, hw, hd, Pi.sub_apply]
      rw [he]
      exact (HeatBackwardDriver.state_norm_sq_sub_le ht.2 hb η f g).trans
        (mul_le_mul_of_nonneg_right (sub_le_sub_left (by exact_mod_cast ht.1.le) _) (sq_nonneg _))
    · rw [show bound t = 0 from indicator_of_notMem ht _]
      rw [indicator_of_notMem ht] at hv hw
      have hz : (fun ω => ‖(v - w) (t, ω)‖ ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) := by
        filter_upwards [hv, hw, hs] with ω hv hw hs
        simp only [hs, Pi.sub_apply, hv, hw, Pi.zero_apply, sub_self, norm_zero,
          zero_pow (by decide : (2 : ℕ) ≠ 0)]
      rw [integral_congr_ae hz, integral_zero]
  refine hle.trans_eq ?_
  rw [show bound = (Ioc a b).indicator (fun _ => C) from rfl, integral_indicator measurableSet_Ioc,
    integral_const, HeatPredictableDriftCell.interval_mass hab hb, smul_eq_mul]
  dsimp [C]
  ring

end HeatBackwardDriverProcess

#print axioms HeatBackwardDriverProcess.exists_state_process
#print axioms HeatBackwardDriverProcess.norm_sq_sub_le
