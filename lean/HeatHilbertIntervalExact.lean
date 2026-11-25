import HeatHilbertCross

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatHilbertIntervalExact
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {T : ℝ≥0}

theorem post_stop_cross_integral (a b : ℝ≥0) (u v : Process (E := C) F μ T) :
    ∀ᵐ ω ∂μ,
      (∫ t, inner ℝ (post F μ T a (stop F μ T b u) (t, ω))
        (post F μ T a (stop F μ T b v) (t, ω)) ∂timeMeasure T) =
      ∫ t in Set.Ioc a b, inner ℝ (u (t, ω)) (v (t, ω)) ∂timeMeasure T := by
  have hpostU := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure T)).quasiMeasurePreserving.ae
    (post_ae F μ T a (stop F μ T b u))
  have hpostV := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure T)).quasiMeasurePreserving.ae
    (post_ae F μ T a (stop F μ T b v))
  have hstopU := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure T)).quasiMeasurePreserving.ae
    (stop_ae F μ T b u)
  have hstopV := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure T)).quasiMeasurePreserving.ae
    (stop_ae F μ T b v)
  filter_upwards [Measure.ae_ae_of_ae_prod hpostU, Measure.ae_ae_of_ae_prod hpostV,
    Measure.ae_ae_of_ae_prod hstopU, Measure.ae_ae_of_ae_prod hstopV] with ω hpu hpv hsu hsv
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [hpu, hpv, hsu, hsv, (timeMeasure T).ae_ne b] with t hpu hpv hsu hsv hne
  dsimp only [Prod.swap] at hpu hpv hsu hsv
  rw [hpu, hpv, hsu, hsv]
  by_cases ha : a < t <;> by_cases hb : t < b
  · have hab : t ∈ Set.Ioc a b := ⟨ha, le_of_lt hb⟩
    simp [ha, hb, hab, before, Set.indicator]
  · have hab : t ∉ Set.Ioc a b := by
      intro h
      exact hne (le_antisymm h.2 (le_of_not_gt hb))
    simp [ha, hb, hab, before, Set.indicator]
  · have hab : t ∉ Set.Ioc a b := fun h => ha h.1
    simp [ha, hb, hab, before, Set.indicator]
  · have hab : t ∉ Set.Ioc a b := fun h => ha h.1
    simp [ha, hb, hab, before, Set.indicator]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem conditional_cross_interval
    (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0} (hab : a ≤ b)
    (u v : Process (E := C) F μ T) :
    μ[(fun ω => inner ℝ
      (J.integral (stop F μ T b u) ω - J.integral (stop F μ T a u) ω)
      (J.integral (stop F μ T b v) ω - J.integral (stop F μ T a v) ω)) | F a] =ᵐ[μ]
    μ[(fun ω => ∫ t in Set.Ioc a b, inner ℝ (u (t, ω)) (v (t, ω)) ∂timeMeasure T) | F a] := by
  have hinc (w : Process (E := C) F μ T) :
      (J.integral (post F μ T a (stop F μ T b w)) : Ω → E) =ᵐ[μ]
      fun ω => J.integral (stop F μ T b w) ω - J.integral (stop F μ T a w) ω := by
    rw [SHE.PastItoAlgebra.post_stop_eq_sub F μ T a b hab, map_sub]
    exact Lp.coeFn_sub _ _
  have hrep : (fun ω => inner ℝ
      (J.integral (post F μ T a (stop F μ T b u)) ω)
      (J.integral (post F μ T a (stop F μ T b v)) ω)) =ᵐ[μ]
      (fun ω => inner ℝ
        (J.integral (stop F μ T b u) ω - J.integral (stop F μ T a u) ω)
        (J.integral (stop F μ T b v) ω - J.integral (stop F μ T a v) ω)) := by
    filter_upwards [hinc u, hinc v] with ω hu hv
    rw [hu, hv]
  exact (condExp_congr_ae (m := F a) hrep).symm.trans
    ((HeatHilbertCross.conditional_cross J hlocal a (stop F μ T b u) (stop F μ T b v)).trans
      (condExp_congr_ae (m := F a) (post_stop_cross_integral a b u v)))

end HeatHilbertIntervalExact

#check @HeatHilbertIntervalExact.post_stop_cross_integral
#print axioms HeatHilbertIntervalExact.post_stop_cross_integral
#check @HeatHilbertIntervalExact.conditional_cross_interval
#print axioms HeatHilbertIntervalExact.conditional_cross_interval
