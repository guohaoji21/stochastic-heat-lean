import HeatTimeLpField
import HeatL2Integrability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatPredictableObservation

open Filter MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E G : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

local notation "ν" => Measure.trim (energyMeasure μ H) (predictable_le_product F)

/-- A bounded spatial operator acts on the predictable control space. -/
def lift (A : E →L[ℝ] G) : Process (E := E) F μ H →L[ℝ] Process (E := G) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact A.compLpL 2 ν

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [IsProbabilityMeasure μ] in
theorem lift_ae (A : E →L[ℝ] G) (v : Process (E := E) F μ H) :
    (lift F μ H A v : ℝ≥0 × Ω → G) =ᵐ[energyMeasure μ H] fun p => A (v p) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ae_eq_of_ae_eq_trim (A.coeFn_compLpL v)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] [IsProbabilityMeasure μ] in
theorem measurable_process (v : Process (E := E) F μ H) : Measurable (v : ℝ≥0 × Ω → E) :=
  ((Lp.stronglyMeasurable v).mono (predictable_le_product F)).measurable

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [IsProbabilityMeasure μ] in
theorem ambient_memLp (v : Process (E := E) F μ H) :
    MemLp (v : ℝ≥0 × Ω → E) 2 (energyMeasure μ H) :=
  memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)

/-- Equality of predictable representatives can be checked on almost all
time sections of the original product measure. -/
theorem eq_of_slices (u v : Process (E := E) F μ H)
    (h : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] fun ω => v (t, ω)) :
    u = v := by
  have he : (u : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] v := (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (measurable_process F μ H u) (measurable_process F μ H v))).mpr h
  apply Lp.ext
  exact ae_eq_trim_of_measurable (predictable_le_product F)
    (Lp.stronglyMeasurable u).measurable (Lp.stronglyMeasurable v).measurable he

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem lift_slices (A : E →L[ℝ] G) (v : Process (E := E) F μ H)
    (V : ℝ≥0 → Lp E 2 μ)
    (hv : ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] V t) :
    ∀ᵐ t ∂timeMeasure H, (fun ω => lift F μ H A v (t, ω)) =ᵐ[μ] (A.compLpL 2 μ) (V t) := by
  filter_upwards [hv, Measure.ae_ae_of_ae_prod (lift_ae F μ H A v)] with t hv hl
  filter_upwards [hv, hl, A.coeFn_compLpL (V t)] with ω hv hl hV
  rw [hl, hv, hV]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem energy (v : Process (E := E) F μ H) (V : ℝ≥0 → Lp E 2 μ)
    (hv : ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] V t) :
    ‖v‖ ^ 2 = ∫ t, ‖V t‖ ^ 2 ∂timeMeasure H := by
  rw [process_integral_energy]
  apply integral_congr_ae
  filter_upwards [hv] with t ht
  rw [realLp_norm_sq]
  exact integral_congr_ae (ht.fun_comp (fun x : E => ‖x‖ ^ 2))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [IsProbabilityMeasure μ] in
private theorem process_inner (u v : Process (E := E) F μ H) :
    inner ℝ u v = ∫ p, inner ℝ (u p) (v p) ∂energyMeasure μ H := by
  rw [L2.inner_def]
  exact (integral_trim (μ := energyMeasure μ H) (predictable_le_product F)
    ((Lp.stronglyMeasurable u).inner (Lp.stronglyMeasurable v))).symm

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The predictable process inner product is the time integral of the
inner products of any actual L² time slices. -/
theorem inner_slices (u v : Process (E := E) F μ H) (U V : ℝ≥0 → Lp E 2 μ)
    (hu : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] U t)
    (hv : ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] V t) :
    inner ℝ u v = ∫ t, inner ℝ (U t) (V t) ∂timeMeasure H := by
  have hi := HeatL2Integrability.inner (energyMeasure μ H)
    (u : ℝ≥0 × Ω → E) (v : ℝ≥0 × Ω → E)
    (ambient_memLp F μ H u) (ambient_memLp F μ H v)
  rw [process_inner]
  have he : (∫ p, inner ℝ (u p) (v p) ∂energyMeasure μ H) =
      ∫ t, ∫ ω, inner ℝ (u (t, ω)) (v (t, ω)) ∂μ ∂timeMeasure H :=
    integral_prod _ hi
  rw [he]
  apply integral_congr_ae
  filter_upwards [hu, hv] with t htu htv
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htu, htv] with ω hωu hωv
  rw [hωu, hωv]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [IsProbabilityMeasure μ] in
theorem lift_inner (A : E →L[ℝ] G) (B : G →L[ℝ] E)
    (h : ∀ x y, inner ℝ (A x) y = inner ℝ x (B y))
    (u : Process (E := E) F μ H) (v : Process (E := G) F μ H) :
    inner ℝ (lift F μ H A u) v = inner ℝ u (lift F μ H B v) := by
  rw [process_inner, process_inner]
  apply integral_congr_ae
  filter_upwards [lift_ae F μ H A u, lift_ae F μ H B v] with p hu hv
  rw [hu, hv, h]

variable [IsSeparable μ]

theorem slice_ae (u : Process (E := E) F μ H) :
    ∀ᵐ t ∂timeMeasure H,
      (fun ω => u (t, ω)) =ᵐ[μ] HeatTimeLpField.value μ u t :=
  (HeatTimeLpField.value_ae μ u (measurable_process F μ H u) H (ambient_memLp F μ H u)).mono
    (fun _ h => h.symm)

end HeatPredictableObservation

#print axioms HeatPredictableObservation.lift_slices
#print axioms HeatPredictableObservation.inner_slices
