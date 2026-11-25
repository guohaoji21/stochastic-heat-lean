import HeatTorusFiniteStochasticAdditive
import HeatControlConvolution
import HeatTimeLpDrift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatTorusFiniteDeterministicAdditive

open Filter MeasureTheory Set SHE.PredictableL2 SHE.StoppedItoInputs
open HeatTorusGalerkinBackward (State laplace)
open HeatTorusProjectedConvolution (finiteHeat finiteHeat_continuous finiteHeat_contraction)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ] (H : ℝ≥0)
  (S : Finset (ι → ℤ)) (P : ℝ)

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

private theorem path_primitive (f : ℝ≥0 → State S) (hf : Measurable f)
    (hfi : Integrable f (timeMeasure H)) {t : ℝ≥0} (ht : t ≤ H) :
    (∫ r, laplace S P (HeatControlConvolution.value H (finiteHeat S P)
      (fun p : ℝ≥0 × Unit => f p.1) r ()) ∂timeMeasure t) =
      HeatControlConvolution.value H (finiteHeat S P) (fun p : ℝ≥0 × Unit => f p.1) t () -
        ∫ s, f s ∂timeMeasure t := by
  let v : ℝ≥0 × Unit → State S := fun p => f p.1
  let A := laplace S P
  let raw : ℝ≥0 × ℝ≥0 → State S := fun p =>
    HeatControlConvolution.raw (finiteHeat S P) v p.1 (p.2, ())
  have hm : Measurable raw :=
    (HeatVolterraKernel.raw_measurable (finiteHeat S P) (ContinuousLinearMap.id ℝ (State S))
      (finiteHeat_continuous S P) (finiteHeat_contraction S P) v (hf.comp measurable_fst)).comp
        (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hb (p : ℝ≥0 × ℝ≥0) : ‖raw p‖ ≤ ‖f p.2‖ :=
    HeatControlConvolution.raw_bound (finiteHeat S P) (finiteHeat_contraction S P) v p.1 (p.2, ())
  have hi : Integrable raw ((timeMeasure t).prod (timeMeasure H)) :=
    (hfi.norm.comp_snd (timeMeasure t)).mono' hm.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hs (r : ℝ≥0) : Integrable (fun s => raw (r, s)) (timeMeasure H) :=
    hfi.norm.mono' ((hm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable)
      (Eventually.of_forall (fun s => hb (r, s)))
  have hiStop : Integrable ((Iio t).indicator f) (timeMeasure H) := hfi.indicator measurableSet_Iio
  change (∫ r, A (∫ s, raw (r, s) ∂timeMeasure H) ∂timeMeasure t) =
    (∫ s, raw (t, s) ∂timeMeasure H) - ∫ s, f s ∂timeMeasure t
  calc
    _ = ∫ r, ∫ s, A (raw (r, s)) ∂timeMeasure H ∂timeMeasure t := by
      apply integral_congr_ae (Eventually.of_forall _)
      intro r
      exact (A.integral_comp_comm (hs r)).symm
    _ = ∫ s, ∫ r, A (raw (r, s)) ∂timeMeasure t ∂timeMeasure H :=
      integral_integral_swap (A.integrable_comp hi)
    _ = ∫ s, (raw (t, s) - (Iio t).indicator f s) ∂timeMeasure H := by
      apply integral_congr_ae (Eventually.of_forall _)
      intro s
      have hk := HeatTorusFiniteStochasticAdditive.kernel_primitive S P v t (s, ())
      change (∫ r, A (raw (r, s)) ∂timeMeasure t) =
        raw (t, s) - (before (t : ℝ)).indicator v (s, ()) at hk
      by_cases hst : s < t
      · rw [indicator_of_mem (show s ∈ Iio t from hst)]
        rw [indicator_of_mem (show (s, ()) ∈ before (t : ℝ) from hst)] at hk
        exact hk
      · rw [indicator_of_notMem (show s ∉ Iio t from hst)]
        rw [indicator_of_notMem (show (s, ()) ∉ before (t : ℝ) from hst)] at hk
        exact hk
    _ = _ := by
      rw [integral_sub (hs t) hiStop, integral_indicator measurableSet_Iio,
        HeatTimeRestriction.restrict_Iio ht]

variable (f : ℝ≥0 × Ω → State S) (hf : Measurable f)
  (hfm : MemLp f 2 (energyMeasure μ H))

private def joint (p : ℝ≥0 × Ω) : State S :=
  HeatControlConvolution.value H (finiteHeat S P) f p.1 p.2

local notation "W" => joint H S P f

def value (t : ℝ≥0) : Lp (State S) 2 μ :=
  (HeatControlConvolution.value_memLp μ H (finiteHeat S P) (finiteHeat_continuous S P)
    (finiteHeat_contraction S P) f hf hfm t).toLp _

omit [IsSeparable μ] in
theorem value_ae (t : ℝ≥0) :
    value μ H S P f hf hfm t =ᵐ[μ] HeatControlConvolution.value H (finiteHeat S P) f t :=
  (HeatControlConvolution.value_memLp μ H (finiteHeat S P) (finiteHeat_continuous S P)
    (finiteHeat_contraction S P) f hf hfm t).coeFn_toLp

include hf in
private theorem joint_measurable : Measurable W := by
  have hm := HeatVolterraKernel.raw_measurable (finiteHeat S P) (ContinuousLinearMap.id ℝ (State S))
    (finiteHeat_continuous S P) (finiteHeat_contraction S P) f hf
  have hr : Measurable (fun q : ℝ≥0 × (ℝ≥0 × Ω) => (q.2.1, (q.1, q.2.2))) :=
    measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  exact ((hm.comp hr).stronglyMeasurable.integral_prod_left' (μ := timeMeasure H)).measurable

omit [IsSeparable μ] in
include hf hfm in
private theorem joint_memLp : MemLp W 2 (energyMeasure μ H) := by
  have hm := joint_measurable H S P f hf
  have hi := (hfm.norm.integrable_sq.integral_prod_right.const_mul (H : ℝ)).comp_snd (timeMeasure H)
  apply (memLp_two_iff_integrable_sq_norm hm.stronglyMeasurable.aestronglyMeasurable).mpr
  apply hi.mono' (hm.stronglyMeasurable.norm.pow 2).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (HeatControlConvolution.time_memLp μ H f hf hfm)]
    with p hp
  change ‖‖W p‖ ^ 2‖ ≤ (H : ℝ) * (∫ s, ‖f (s, p.2)‖ ^ 2 ∂timeMeasure H)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact HeatControlConvolution.energy_pointwise H (finiteHeat S P) (finiteHeat_continuous S P)
    (finiteHeat_contraction S P) f hf p.2 hp p.1

theorem square_integrable : MemLp (value μ H S P f hf hfm) 2 (timeMeasure H) := by
  have hm := joint_measurable H S P f hf
  have hi := joint_memLp μ H S P f hf hfm
  apply (HeatTimeLpField.square_integrable μ W hm H hi).ae_eq
  filter_upwards [HeatTimeLpField.value_ae μ W hm H hi] with t ht
  exact Lp.ext (ht.trans (value_ae μ H S P f hf hfm t).symm)

/-- The deterministic mild convolution satisfies the additive Galerkin equation in L². -/
theorem additive {t : ℝ≥0} (ht : t ≤ H) :
    value μ H S P f hf hfm t = HeatAmbientDrift.value μ H f hf hfm t +
      ∫ r, ((laplace S P).compLpL 2 μ) (value μ H S P f hf hfm r) ∂timeMeasure t := by
  let A := laplace S P
  let wa := value μ H S P f hf hfm
  let : IsFiniteMeasure (energyMeasure μ t) := by unfold energyMeasure; infer_instance
  have hW : Integrable W (energyMeasure μ t) :=
    ((joint_memLp μ H S P f hf hfm).mono_measure
      (Measure.prod_mono (HeatTimeRestriction.mono ht) le_rfl)).integrable one_le_two
  have hwa := ((square_integrable μ H S P f hf hfm).mono_measure
    (HeatTimeRestriction.mono ht)).integrable one_le_two
  have hrep : ∀ᵐ r ∂timeMeasure t, (A.compLpL 2 μ) (wa r) =ᵐ[μ] fun ω => A (W (r, ω)) :=
    Eventually.of_forall fun r => (A.coeFn_compLpL (wa r)).trans
      ((value_ae μ H S P f hf hfm r).fun_comp A)
  have hF := SHE.LpIntegralFubini.integral_ae μ (timeMeasure t)
    (fun r => (A.compLpL 2 μ) (wa r)) ((A.compLpL 2 μ).integrable_comp hwa)
    (fun p => A (W p)) (A.integrable_comp hW) hrep
  apply Lp.ext
  filter_upwards [value_ae μ H S P f hf hfm t, hF,
    Lp.coeFn_add (HeatAmbientDrift.value μ H f hf hfm t)
      (∫ r, (A.compLpL 2 μ) (wa r) ∂timeMeasure t),
    HeatAmbientDrift.value_ae μ H f hf hfm ht, HeatControlConvolution.time_memLp μ H f hf hfm]
    with ω hv hi hadd hfω hsω
  change wa t ω = _
  rw [hv, hadd, Pi.add_apply, hi, hfω]
  have hprim := path_primitive H S P (fun s => f (s, ω))
    (hf.comp (measurable_id.prodMk measurable_const)) (hsω.integrable one_le_two) ht
  change (∫ r, A (W (r, ω)) ∂timeMeasure t) = W (t, ω) - ∫ s, f (s, ω) ∂timeMeasure t at hprim
  change W (t, ω) = _
  rw [hprim]
  abel

end HeatTorusFiniteDeterministicAdditive

#print axioms HeatTorusFiniteDeterministicAdditive.additive
