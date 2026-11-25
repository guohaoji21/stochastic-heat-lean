import HeatBochnerCell
import SHE.ProcessEnergy
import BrownianMotion.StochasticIntegral.Predictable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace HeatPredictableDriftCell

open Filter MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

private theorem measurable_process (f : Process (E := E) F μ H) :
    Measurable (f : ℝ≥0 × Ω → E) :=
  ((Lp.stronglyMeasurable f).mono (predictable_le_product F)).measurable

private theorem memLp_process (f : Process (E := E) F μ H) :
    MemLp (f : ℝ≥0 × Ω → E) 2 (energyMeasure μ H) :=
  memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp f)

/-- The Bochner drift integral over a deterministic time cell as an L² random variable. -/
def value (a b : ℝ≥0) (f : Process (E := E) F μ H) : Lp E 2 μ :=
  (HeatBochnerCell.square_integrable μ H f (measurable_process f) (memLp_process f) a b).toLp
    (HeatBochnerCell.value H f a b)

theorem value_ae (a b : ℝ≥0) (f : Process (E := E) F μ H) :
    (value a b f : Ω → E) =ᵐ[μ] HeatBochnerCell.value H f a b :=
  MemLp.coeFn_toLp _

theorem adapted (a b : ℝ≥0) (f : Process (E := E) F μ H) :
    AEStronglyMeasurable[F b] (value a b f : Ω → E) μ := by
  have hp : IsStronglyPredictable F (Function.curry f) := Lp.stronglyMeasurable f
  have hpast := hp.isStronglyProgressive b
  letI : MeasurableSpace Ω := F b
  have hclock : Measurable (fun p : ℝ≥0 × Ω => (⟨min p.1 b, min_le_right p.1 b⟩ : Iic b)) :=
    (measurable_fst.min measurable_const).subtype_mk
  have hf : StronglyMeasurable (fun p : ℝ≥0 × Ω => f (min p.1 b, p.2)) :=
    hpast.comp_measurable (hclock.prodMk measurable_snd)
  have hi : MeasurableSet (Prod.fst ⁻¹' Ioc a b : Set (ℝ≥0 × Ω)) :=
    measurableSet_Ioc.preimage measurable_fst
  have he (ω : Ω) : (∫ s, (Prod.fst ⁻¹' Ioc a b : Set (ℝ≥0 × Ω)).indicator
      (fun p => f (min p.1 b, p.2)) (s, ω) ∂timeMeasure H) = HeatBochnerCell.value H f a b ω := by
    change (∫ s, (Ioc a b).indicator (fun s => f (min s b, ω)) s ∂timeMeasure H) = _
    rw [integral_indicator measurableSet_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change f (min s b, ω) = f (s, ω)
    rw [min_eq_left hs.2]
  have hm : StronglyMeasurable[F b] (HeatBochnerCell.value H f a b) := by
    rw [← funext he]
    exact (hf.indicator hi).integral_prod_left'
  letI : MeasurableSpace Ω := mΩ
  exact hm.aestronglyMeasurable.congr (value_ae a b f).symm

theorem sub (a b : ℝ≥0) (f g : Process (E := E) F μ H) :
    value a b (f - g) = value a b f - value a b g := by
  have hfg := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (ae_eq_of_ae_eq_trim (Lp.coeFn_sub f g))
  apply Lp.ext
  filter_upwards [Measure.ae_ae_of_ae_prod hfg, value_ae a b (f - g), value_ae a b f, value_ae a b g,
    Lp.coeFn_sub (value a b f) (value a b g),
    HeatControlConvolution.time_memLp μ H f (measurable_process f) (memLp_process f),
    HeatControlConvolution.time_memLp μ H g (measurable_process g) (memLp_process g)]
    with ω hfg hd hf hg hs hfi hgi
  rw [hd, hs, Pi.sub_apply, hf, hg]
  unfold HeatBochnerCell.value
  rw [← integral_sub ((hfi.integrable one_le_two).integrableOn) ((hgi.integrable one_le_two).integrableOn)]
  apply integral_congr_ae
  exact ae_mono Measure.restrict_le_self hfg

theorem split {a b c : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (f : Process (E := E) F μ H) :
    value a c f = value a b f + value b c f := by
  have hu : Ioc a b ∪ Ioc b c = Ioc a c := Ioc_union_Ioc_eq_Ioc hab hbc
  have hd : Disjoint (Ioc a b) (Ioc b c) :=
    Set.disjoint_left.mpr fun _ h₁ h₂ => not_lt_of_ge h₁.2 h₂.1
  apply Lp.ext
  filter_upwards [value_ae a c f, value_ae a b f, value_ae b c f,
    Lp.coeFn_add (value a b f) (value b c f),
    HeatControlConvolution.time_memLp μ H f (measurable_process f) (memLp_process f)]
    with ω hc hb ha hsum hfi
  rw [hc, hsum, Pi.add_apply, hb, ha]
  unfold HeatBochnerCell.value
  rw [← hu, setIntegral_union hd measurableSet_Ioc
    (hfi.integrable one_le_two).integrableOn (hfi.integrable one_le_two).integrableOn]

@[simp]
theorem self (a : ℝ≥0) (f : Process (E := E) F μ H) : value a a f = 0 := by
  apply Lp.ext
  filter_upwards [value_ae a a f, Lp.coeFn_zero E 2 μ] with ω hf hz
  rw [hf, hz]
  simp [HeatBochnerCell.value]

theorem interval_mass {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H) :
    ((timeMeasure H).restrict (Ioc a b)).real univ = (b : ℝ) - a := by
  have he : (intervalTimeMeasure a b) univ =
      (volume : Measure ℝ).restrict (Ioc (a : ℝ) b) univ := by
    rw [← intervalTimeMeasure_map, Measure.map_apply measurable_coe_nnreal_real MeasurableSet.univ, preimage_univ]
  rw [timeMeasure_restrict_Ioc a hb, Measure.real, he, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hab))]

/-- The deterministic cell integral has norm at most the square root of the cell length. -/
theorem norm_sq_le {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H)
    (f : Process (E := E) F μ H) :
    ‖value a b f‖ ^ 2 ≤ ((b : ℝ) - a) * ‖f‖ ^ 2 := by
  have he := HeatBochnerCell.energy μ H f (measurable_process f) (memLp_process f) a b
  rw [interval_mass hab hb] at he
  refine he.trans (mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr (by exact_mod_cast hab)))
  rw [subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F)]
  have hf := (memLp_process f).norm.integrable_sq
  apply integral_mono_ae
    (hf.indicator (measurableSet_Ioc.preimage measurable_fst)) hf
  apply Eventually.of_forall
  intro p
  by_cases h : p ∈ Prod.fst ⁻¹' Ioc a b
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]
    exact sq_nonneg _

end HeatPredictableDriftCell

#print axioms HeatPredictableDriftCell.adapted
#print axioms HeatPredictableDriftCell.norm_sq_le
#print axioms HeatPredictableDriftCell.split
