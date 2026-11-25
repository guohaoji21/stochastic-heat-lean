import HeatVolterraSolutionLinear
import HeatPredictableDriftLinear
import HeatProgressiveControl
import HeatVersionLp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatPredictableControlConvolution

open Filter MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

local notation "Proc" => Process (E := E) F μ H

/-- The deterministic convolution at a fixed time, acting on actual
predictable L² controls. -/
def atTime (t : ℝ≥0) : Proc →L[ℝ] Lp E 2 μ :=
  (HeatPredictableDriftLinear.integral F μ H).comp
    (HeatVolterraSolutionLinear.sliceOperator F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) t)

include hS hcontr in
theorem atTime_ae (t : ℝ≥0) (f : Proc) :
    (atTime F μ H S hS hcontr t f : Ω → E) =ᵐ[μ] HeatControlConvolution.value H S f t := by
  let z := HeatVolterraSlice.slice F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) t f
  have h := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (HeatVolterraSlice.slice_ae F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) t f)
  change (HeatPredictableDriftCell.value 0 H z : Ω → E) =ᵐ[μ] _
  filter_upwards [HeatPredictableDriftCell.value_ae 0 H z, Measure.ae_ae_of_ae_prod h] with ω hz hs
  rw [hz]
  unfold HeatBochnerCell.value HeatControlConvolution.value
  rw [timeMeasure_restrict_Ioc 0 (show H ≤ H from le_rfl)]
  exact integral_congr_ae hs

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsProbabilityMeasure μ] in
private theorem clamp_eq (f : Proc) :
    HeatControlAdapted.clamp (Function.curry f) H =ᵐ[energyMeasure μ H] f := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
  change f (min p.1 H, p.2) = f p
  rw [min_eq_left hp.2]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem control_clamp_ae (f : Proc) (t : ℝ≥0) :
    HeatControlConvolution.value H S (HeatControlAdapted.clamp (Function.curry f) H) t =ᵐ[μ]
      HeatControlConvolution.value H S f t := by
  have he := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (clamp_eq F μ H f)
  filter_upwards [Measure.ae_ae_of_ae_prod he] with ω hω
  unfold HeatControlConvolution.value
  apply integral_congr_ae
  filter_upwards [hω] with s hs
  change HeatControlAdapted.clamp (Function.curry f) H (s, ω) = f (s, ω) at hs
  simp only [HeatControlConvolution.raw, HeatVolterraKernel.raw, hs]

include hS hcontr in
theorem atTime_zero (f : Proc) : atTime F μ H S hS hcontr 0 f = 0 := by
  apply Lp.ext
  filter_upwards [atTime_ae F μ H S hS hcontr 0 f, Lp.coeFn_zero E 2 μ] with ω hf hz
  rw [hf, hz]
  simp only [HeatControlConvolution.value, HeatControlConvolution.raw, HeatVolterraKernel.raw,
    not_lt_zero, ite_false, integral_zero, Pi.zero_apply]

variable (hn : NullCompleteFiltration.ContainsNullSets F μ)
include hn

include hS hcontr in
private theorem exists_realization (f : Proc) :
    ∃ v : Proc, ∃ X : ℝ≥0 → Ω → E,
      (∀ ω, Continuous (fun t => X t ω)) ∧ StronglyAdapted F X ∧
      (v : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] Function.uncurry X ∧
      (∀ t, (atTime F μ H S hS hcontr t f : Ω → E) =ᵐ[μ] X t) ∧
      ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧ (∀ t ω, ‖X t ω‖ ≤ D ω) := by
  let U := Function.curry (f : ℝ≥0 × Ω → E)
  have hU : IsStronglyPredictable F U := Lp.stronglyMeasurable f
  have hf := (HeatPredictableObservation.ambient_memLp F μ H f).norm.integrable_sq
  obtain ⟨v, X, hc, ha, _, hv, hX, D, hD, hD0, hDb, _⟩ :=
    HeatProgressiveControl.exists_version F μ H S hS hcontr hn U hU.isStronglyProgressive hf
  refine ⟨v, X, hc, ha, hv, fun t => ?_, D, hD, hD0, hDb⟩
  exact (atTime_ae F μ H S hS hcontr t f).trans
    ((control_clamp_ae F μ H S f t).symm.trans (hX t).symm)

include hS hcontr in
private theorem exists_process (f : Proc) :
    ∃ v : Proc, ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] atTime F μ H S hS hcontr t f := by
  obtain ⟨v, X, _, _, hv, hX, _⟩ := exists_realization F μ H S hS hcontr hn f
  refine ⟨v, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hv] with t ht
  exact (show (fun ω => v (t, ω)) =ᵐ[μ] X t from ht).trans (hX t).symm

private def process (f : Proc) : Proc := Classical.choose (exists_process F μ H S hS hcontr hn f)

include hS hcontr in
private theorem process_slices (f : Proc) :
    ∀ᵐ t ∂timeMeasure H, (fun ω => process F μ H S hS hcontr hn f (t, ω)) =ᵐ[μ]
      atTime F μ H S hS hcontr t f :=
  Classical.choose_spec (exists_process F μ H S hS hcontr hn f)

/-- The deterministic heat convolution as a bounded linear operator in
the ordinary predictable product-L² space. -/
def convolution : Proc →L[ℝ] Proc := by
  let v := process F μ H S hS hcontr hn
  let hv := process_slices F μ H S hS hcontr hn
  let K := atTime F μ H S hS hcontr
  let lin : Proc →ₗ[ℝ] Proc :=
    { toFun := v
      map_add' := fun f g => by
        apply HeatPredictableObservation.eq_of_slices F μ H
        filter_upwards [hv (f + g), hv f, hv g, Measure.ae_ae_of_ae_prod
          (ae_eq_of_ae_eq_trim (Lp.coeFn_add (v f) (v g)))] with t h hf hg hfg
        rw [map_add] at h
        filter_upwards [h, hf, hg, hfg, Lp.coeFn_add (K t f) (K t g)] with ω h hf hg hfg hl
        rw [h, hl, hfg, Pi.add_apply, Pi.add_apply, hf, hg]
      map_smul' := fun c f => by
        apply HeatPredictableObservation.eq_of_slices F μ H
        filter_upwards [hv (c • f), hv f, Measure.ae_ae_of_ae_prod
          (ae_eq_of_ae_eq_trim (Lp.coeFn_smul c (v f)))] with t h hf hcf
        rw [map_smul] at h
        filter_upwards [h, hf, hcf, Lp.coeFn_smul c (K t f)] with ω h hf hcf hl
        change v (c • f) (t, ω) = (c • v f) (t, ω)
        rw [h, hl, hcf, Pi.smul_apply, Pi.smul_apply, hf] }
  refine lin.mkContinuous (H : ℝ) fun f => ?_
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg H.property (norm_nonneg _))).mp
  have h := HeatVolterraUniformEnergy.control_energy F μ H S hS hcontr (f : ℝ≥0 × Ω → E)
    (HeatPredictableObservation.measurable_process F μ H f)
    (HeatPredictableObservation.ambient_memLp F μ H f) (v f) (by
      filter_upwards [hv f] with t ht
      exact ht.trans (atTime_ae F μ H S hS hcontr t f))
  rw [mul_pow, subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F) f]
  exact h

include hS hcontr in
theorem convolution_slices (f : Proc) :
    ∀ᵐ t ∂timeMeasure H, (fun ω => convolution F μ H S hS hcontr hn f (t, ω)) =ᵐ[μ]
      atTime F μ H S hS hcontr t f :=
  process_slices F μ H S hS hcontr hn f

include hS hcontr in
theorem atTime_regular [Nontrivial E] (f : Proc) :
    Continuous (fun t => atTime F μ H S hS hcontr t f) ∧
      ∀ t, ∃ X : Ω → E, StronglyMeasurable[F t] X ∧
        (atTime F μ H S hS hcontr t f : Ω → E) =ᵐ[μ] X := by
  obtain ⟨_, X, hc, ha, _, hX, D, hD, hD0, hDb⟩ := exists_realization F μ H S hS hcontr hn f
  let hm (t : ℝ≥0) := (ha t).mono (F.le t)
  have h (t : ℝ≥0) : atTime F μ H S hS hcontr t f = HeatVersionLp.value μ X hm D hD hDb t :=
    Lp.ext ((hX t).trans (HeatVersionLp.value_ae μ X hm D hD hDb t).symm)
  refine ⟨?_, fun t => ⟨X t, ha t, hX t⟩⟩
  simp_rw [h]
  exact HeatVersionLp.continuous μ X hm D hD hD0 hDb hc

end HeatPredictableControlConvolution

#print axioms HeatPredictableControlConvolution.atTime_ae
#print axioms HeatPredictableControlConvolution.convolution_slices
#print axioms HeatPredictableControlConvolution.atTime_regular
