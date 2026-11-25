import HeatBackwardDriverProcess
import HeatPredictableLinearMap
import SHE.StoppedInputAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatBackwardCellSupport

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

abbrev Supported (a b : ℝ≥0) (u : Process (E := E) F μ H) : Prop :=
  ∀ᵐ p ∂energyMeasure μ H, p.1 ∉ Ioc a b → u p = 0

theorem of_stops {a b : ℝ≥0} {u : Process (E := E) F μ H}
    (ha : stop F μ H a u = 0) (hb : stop F μ H b u = u) : Supported a b u := by
  have hzero := stop_ae F μ H a u
  rw [ha] at hzero
  have hend := stop_ae F μ H b u
  rw [hb] at hend
  filter_upwards [hzero, hend, ae_eq_of_ae_eq_trim (Lp.coeFn_zero E 2
      ((energyMeasure μ H).trim (predictable_le_product F))),
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne a)] with p h₁ h₂ hz hne hp
  by_cases hpa : p.1 ≤ a
  · have hlt : p.1 < a := lt_of_le_of_ne hpa hne
    rw [indicator_of_mem (show p ∈ before (a : ℝ) by exact_mod_cast hlt), hz] at h₁
    exact h₁.symm
  · have hpb : b < p.1 := lt_of_not_ge fun hpb => hp ⟨lt_of_not_ge hpa, hpb⟩
    have hnot : p ∉ before (b : ℝ) := by
      change ¬ (p.1 : ℝ) < b
      exact_mod_cast (not_lt_of_ge hpb.le)
    rw [indicator_of_notMem hnot] at h₂
    exact h₂

theorem stops {a b : ℝ≥0} {u : Process (E := E) F μ H} (hu : Supported a b u) :
    stop F μ H a u = 0 ∧ stop F μ H b u = u := by
  constructor
  · apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [stop_ae F μ H a u, hu, ae_eq_of_ae_eq_trim (Lp.coeFn_zero E 2
      ((energyMeasure μ H).trim (predictable_le_product F)))] with p hstop hu hz
    rw [hstop, hz]
    by_cases hp : p ∈ before (a : ℝ)
    · have hlt : p.1 < a := by exact_mod_cast hp
      rw [indicator_of_mem hp, hu (fun h => (not_lt_of_ge hlt.le) h.1)]
      rfl
    · rw [indicator_of_notMem hp]
      rfl
  · apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [stop_ae F μ H b u, hu,
      Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne b)] with p hstop hu hne
    rw [hstop]
    by_cases hp : p ∈ before (b : ℝ)
    · rw [indicator_of_mem hp]
    · have hle : b ≤ p.1 := by
        change ¬ (p.1 : ℝ) < b at hp
        exact_mod_cast (le_of_not_gt hp)
      rw [indicator_of_notMem hp, hu (fun h => hne (le_antisymm h.2 hle))]

private theorem measurable_process (u : Process (E := E) F μ H) :
    Measurable (u : ℝ≥0 × Ω → E) :=
  ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable

theorem of_state {a b : ℝ≥0} {η : Lp E 2 μ} {f u : Process (E := E) F μ H}
    (hu : HeatBackwardDriverProcess.Realizes a b η f u) : Supported a b u := by
  let C : Set (ℝ≥0 × Ω) := (Prod.fst ⁻¹' Ioc a b)ᶜ
  have hm : Measurable (C.indicator (u : ℝ≥0 × Ω → E)) :=
    (measurable_process u).indicator ((measurableSet_Ioc.preimage measurable_fst).compl)
  have he : C.indicator (u : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] fun _ => 0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const)).mpr
    filter_upwards [hu] with t hut
    by_cases ht : t ∈ Ioc a b
    · exact Eventually.of_forall fun ω => indicator_of_notMem (show (t, ω) ∉ C from fun hp => hp ht) _
    · rw [indicator_of_notMem ht] at hut
      filter_upwards [hut] with ω hω
      rw [indicator_of_mem (show (t, ω) ∈ C from ht)]
      exact hω
  filter_upwards [he] with p hp hn
  exact (indicator_of_mem (show p ∈ C from hn) _).symm.trans hp

theorem map {a b : ℝ≥0} {u : Process (E := E) F μ H} (hu : Supported a b u) (A : E →L[ℝ] E) :
    Supported a b (HeatPredictableLinearMap.map F μ H A u) := by
  filter_upwards [hu, HeatPredictableLinearMap.map_ae F μ H A u] with p h₁ h₂ hp
  rw [h₂, h₁ hp, map_zero]

theorem add {a c b : ℝ≥0} {u v : Process (E := E) F μ H}
    (hac : a ≤ c) (hcb : c ≤ b) (hu : Supported a c u) (hv : Supported c b v) :
    Supported a b (u + v) := by
  filter_upwards [hu, hv, ae_eq_of_ae_eq_trim (Lp.coeFn_add u v)] with p hu hv he hp
  rw [he, Pi.add_apply, hu (fun h => hp ⟨h.1, h.2.trans hcb⟩),
    hv (fun h => hp ⟨hac.trans_lt h.1, h.2⟩), zero_add]

theorem same_add {a b : ℝ≥0} {u v : Process (E := E) F μ H}
    (hu : Supported a b u) (hv : Supported a b v) : Supported a b (u + v) := by
  filter_upwards [hu, hv, ae_eq_of_ae_eq_trim (Lp.coeFn_add u v)] with p hu hv he hp
  rw [he, Pi.add_apply, hu hp, hv hp, zero_add]

theorem drift_zero {a b c d : ℝ≥0} {u : Process (E := E) F μ H}
    (hu : Supported a b u) (h : Disjoint (Ioc a b) (Ioc c d)) :
    HeatPredictableDriftCell.value c d u = 0 := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hu
  apply Lp.ext
  filter_upwards [HeatPredictableDriftCell.value_ae c d u, Lp.coeFn_zero E 2 μ,
    Measure.ae_ae_of_ae_prod hs] with ω hv hz hs
  rw [hv, hz]
  change (∫ s in Ioc c d, u (s, ω) ∂timeMeasure H) = 0
  apply integral_eq_zero_of_ae
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [hs] with s hs hsd
  exact hs (fun hsb => Set.disjoint_left.mp h hsb hsd)

theorem drift_add (a b : ℝ≥0) (u v : Process (E := E) F μ H) :
    HeatPredictableDriftCell.value a b (u + v) =
      HeatPredictableDriftCell.value a b u + HeatPredictableDriftCell.value a b v := by
  have h := HeatPredictableDriftCell.sub a b (u + v) v
  rw [add_sub_cancel_right] at h
  exact sub_eq_iff_eq_add.mp h.symm

theorem post_eq_of_le {a b t : ℝ≥0} {u : Process (E := E) F μ H}
    (hta : t ≤ a) (hu : Supported a b u) : post F μ H t u = u := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [hu, post_ae F μ H t u] with p hu hp
  rw [hp]
  by_cases h : t < p.1
  · rw [if_pos h]
  · exact (if_neg h).trans (hu (fun ha => h (hta.trans_lt ha.1))).symm

theorem post_zero_of_ge {a b t : ℝ≥0} {u : Process (E := E) F μ H}
    (hbt : b ≤ t) (hu : Supported a b u) : post F μ H t u = 0 := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [hu, post_ae F μ H t u, ae_eq_of_ae_eq_trim (Lp.coeFn_zero E 2
      ((energyMeasure μ H).trim (predictable_le_product F)))] with p hu hp hz
  rw [hp, hz]
  by_cases h : t < p.1
  · rw [if_pos h, hu (fun hb => not_lt_of_ge hb.2 (hbt.trans_lt h))]
    rfl
  · rw [if_neg h]
    rfl

end HeatBackwardCellSupport

#print axioms HeatBackwardCellSupport.of_state
#print axioms HeatBackwardCellSupport.drift_zero
