import HeatStoppedMartingale
import HeatTimeRestriction
import HeatItoNormEnergy
import HeatStoppedSliceEnergy
import SHEStochastic.FiniteItoStoppedVersions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section

namespace HeatTerminalItoCompression

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.PastItoInputs
open scoped NNReal ENNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {T H : ℝ≥0}

private abbrev processMeasure (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0) :=
  (energyMeasure μ h).trim (predictable_le_product F)

theorem restrict_energy (μ : Measure Ω) [IsProbabilityMeasure μ] (hTH : T ≤ H) :
    (energyMeasure μ H).restrict (before (Ω := Ω) T) = energyMeasure μ T := by
  have hset : before (Ω := Ω) (T : ℝ) = (Iio T) ×ˢ (univ : Set Ω) := by
    ext p
    simp [before]
  rw [hset, energyMeasure, energyMeasure, ← Measure.restrict_prod_eq_prod_univ, HeatTimeRestriction.restrict_Iio hTH]

private theorem restrict_trimmed (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hTH : T ≤ H) :
    (processMeasure F μ H).restrict (before (Ω := Ω) T) = processMeasure F μ T := by
  rw [processMeasure, restrict_trim _ _ (before_measurable F T), restrict_energy μ hTH]

private def shorten (hTH : T ≤ H) (v : Process (E := C) F μ H) : Process (E := C) F μ T :=
  ((Lp.memLp v).mono_measure (by
    change processMeasure F μ T ≤ processMeasure F μ H
    rw [← restrict_trimmed F μ hTH]
    exact Measure.restrict_le_self)).toLp v

private theorem shorten_ae (hTH : T ≤ H) (v : Process (E := C) F μ H) :
    shorten hTH v =ᵐ[processMeasure F μ T] v := MemLp.coeFn_toLp _

private theorem memLp_extend (hTH : T ≤ H) (v : Process (E := C) F μ T) :
    MemLp ((before (T : ℝ)).indicator v) 2 (processMeasure F μ H) :=
  (memLp_indicator_iff_restrict (before_measurable F T).nullMeasurableSet).2 (by
    rw [restrict_trimmed F μ hTH]
    exact Lp.memLp v)

private def extend (hTH : T ≤ H) (v : Process (E := C) F μ T) : Process (E := C) F μ H :=
  (memLp_extend hTH v).toLp ((before (T : ℝ)).indicator v)

private theorem extend_ae (hTH : T ≤ H) (v : Process (E := C) F μ T) :
    extend hTH v =ᵐ[processMeasure F μ H] (before (T : ℝ)).indicator v := MemLp.coeFn_toLp _

private theorem ae_before_of_small (hTH : T ≤ H) {p : ℝ≥0 × Ω → Prop}
    (hp : ∀ᵐ x ∂processMeasure F μ T, p x) :
    ∀ᵐ x ∂processMeasure F μ H, x ∈ before (T : ℝ) → p x :=
  (ae_restrict_iff' (before_measurable F T)).mp (by rwa [restrict_trimmed F μ hTH])

/-- Zero extension of predictable inputs extends the time horizon isometrically. -/
def extendIsometry (hTH : T ≤ H) : Process (E := C) F μ T →ₗᵢ[ℝ] Process (E := C) F μ H where
  toFun := extend hTH
  map_add' u v := by
    apply Lp.ext
    filter_upwards [extend_ae hTH (u + v), extend_ae hTH u, extend_ae hTH v,
      Lp.coeFn_add (extend hTH u) (extend hTH v), ae_before_of_small hTH (Lp.coeFn_add u v)]
      with p hsum hu hv hadd hsmall
    rw [hsum, hadd, Pi.add_apply, hu, hv]
    by_cases hp : p ∈ before (T : ℝ)
    · simp only [indicator_of_mem hp, hsmall hp, Pi.add_apply]
    · simp [indicator_of_notMem hp]
  map_smul' a u := by
    apply Lp.ext
    filter_upwards [extend_ae hTH (a • u), extend_ae hTH u,
      Lp.coeFn_smul a (extend hTH u), ae_before_of_small hTH (Lp.coeFn_smul a u)]
      with p hs hu hbig hsmall
    rw [RingHom.id_apply, hs, hbig, Pi.smul_apply, hu]
    by_cases hp : p ∈ before (T : ℝ)
    · simp only [indicator_of_mem hp, hsmall hp, Pi.smul_apply]
    · simp [indicator_of_notMem hp]
  norm_map' u := by
    change ‖extend hTH u‖ = ‖u‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (extend_ae hTH u),
      eLpNorm_indicator_eq_eLpNorm_restrict (before_measurable F T).nullMeasurableSet,
      restrict_trimmed F μ hTH]

theorem extend_shorten_eq_stop (hTH : T ≤ H) (v : Process (E := C) F μ H) :
    extendIsometry hTH (shorten hTH v) = stop F μ H T v := by
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [ae_eq_of_ae_eq_trim (extend_ae hTH (shorten hTH v)), stop_ae F μ H T v,
    (ae_restrict_iff' ((predictable_le_product F) _ (before_measurable F T))).mp (by
      rw [restrict_energy μ hTH]
      exact ae_eq_of_ae_eq_trim (shorten_ae hTH v))] with p he hs hr
  change extend hTH (shorten hTH v) p = stop F μ H T v p
  rw [he, hs]
  by_cases hp : p ∈ before (T : ℝ)
  · simp only [indicator_of_mem hp, hr hp]
  · simp [indicator_of_notMem hp]

theorem extend_stop_constant (hTH : T ≤ H) {t : ℝ≥0} (ht : t ≤ T) (c : C) :
    extendIsometry hTH (stop F μ T t (RotatedCylindricalCoordinates.constant F μ T c)) =
      stop F μ H t (RotatedCylindricalCoordinates.constant F μ H c) := by
  let u := RotatedCylindricalCoordinates.constant F μ T c
  let v := RotatedCylindricalCoordinates.constant F μ H c
  have hsmall : ∀ᵐ p ∂energyMeasure μ T, stop F μ T t u p = (before (t : ℝ)).indicator (fun _ => c) p := by
    filter_upwards [stop_ae F μ T t u, RotatedCylindricalCoordinates.constant_ae F μ T c]
      with p hs hu
    rw [hs]
    by_cases hp : p ∈ before (t : ℝ)
    · simpa only [indicator_of_mem hp] using hu
    · simp only [indicator_of_notMem hp]
  have hsmall' := (ae_restrict_iff' ((predictable_le_product F) _ (before_measurable F T))).mp
    (show ∀ᵐ p ∂(energyMeasure μ H).restrict (before (T : ℝ)),
      stop F μ T t u p = (before (t : ℝ)).indicator (fun _ => c) p by
      rw [restrict_energy μ hTH]
      exact hsmall)
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [ae_eq_of_ae_eq_trim (extend_ae hTH (stop F μ T t u)), hsmall',
    stop_ae F μ H t v, RotatedCylindricalCoordinates.constant_ae F μ H c] with p he hs hv hc
  change extend hTH (stop F μ T t u) p = stop F μ H t v p
  rw [he, hv]
  by_cases hp : p ∈ before (T : ℝ)
  · rw [indicator_of_mem hp, hs hp]
    by_cases hpt : p ∈ before (t : ℝ)
    · simpa only [indicator_of_mem hpt] using hc.symm
    · simp only [indicator_of_notMem hpt]
  · have hpt : p ∉ before (t : ℝ) := fun hpt => hp (hpt.trans_le (NNReal.coe_le_coe.mpr ht))
    simp only [indicator_of_notMem hp, indicator_of_notMem hpt]

/-- One representation on a larger horizon suffices for a terminal value
that is measurable at `T`. The future integrand vanishes by Itô injectivity. -/
theorem integral_eq_stopped_of_measurable (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (hTH : T ≤ H) (v : Process (E := C) F μ H)
    (hv : AEStronglyMeasurable[F T] (J.integral v : Ω → E) μ) :
    J.integral v = J.integral (stop F μ H T v) := by
  have hce := HeatStoppedMartingale.conditional_stopped J hJ hTH v
  rw [SHEStochastic.FiniteItoStoppedVersions.stop_horizon] at hce
  have hid := condExp_of_aestronglyMeasurable' (F.le T) hv ((Lp.memLp (J.integral v)).integrable one_le_two)
  exact Lp.ext (hid.symm.trans hce)

theorem restrict_representation (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (hTH : T ≤ H) (X : Lp E 2 μ)
    (hX : AEStronglyMeasurable[F T] (X : Ω → E) μ)
    (hrep : ∃ v : Process (E := C) F μ H, J.integral v = X) :
    ∃ u : Process (E := C) F μ T, J.integral (extendIsometry hTH u) = X := by
  obtain ⟨v, hv⟩ := hrep
  have hs : J.integral v = J.integral (stop F μ H T v) :=
    integral_eq_stopped_of_measurable J hJ hTH v (by rwa [hv])
  exact ⟨shorten hTH v, by rw [extend_shorten_eq_stop, ← hs, hv]⟩

/-- Use the same terminal Itô map on inputs from the shorter horizon.
Its adaptation and centering follow from the corresponding long-horizon properties. -/
def restrictTerminal (J : StandardTerminalIto (C := C) (E := E) F μ H) (hTH : T ≤ H) :
    StandardTerminalIto (C := C) (E := E) F μ T where
  integral := J.integral.comp (extendIsometry hTH)
  adapted t v hv := by
    apply J.adapted t (extendIsometry hTH v)
    have hp := (ae_restrict_iff' ((predictable_le_product F) _ (before_measurable F T))).mp (by
      rw [restrict_energy μ hTH]
      exact hv)
    filter_upwards [ae_eq_of_ae_eq_trim (extend_ae hTH v), hp] with p he hp ht
    change extend hTH v p = 0
    rw [he]
    by_cases h : p ∈ before (T : ℝ)
    · rw [indicator_of_mem h, hp h ht]
    · rw [indicator_of_notMem h]
  centered v := J.centered (extendIsometry hTH v)

private theorem extend_eventProcess (hTH : T ≤ H) (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[F s] A)
    (u : Process (E := C) F μ T) :
    extendIsometry hTH (eventProcess F μ T s A hA u) = eventProcess F μ H s A hA (extendIsometry hTH u) := by
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  have h₀ := (ae_restrict_iff' ((predictable_le_product F) _ (before_measurable F T))).mp (by
    rw [restrict_energy μ hTH]
    exact eventProcess_ae F μ T s A hA u)
  filter_upwards [ae_eq_of_ae_eq_trim (extend_ae hTH (eventProcess F μ T s A hA u)),
    ae_eq_of_ae_eq_trim (extend_ae hTH u), eventProcess_ae F μ H s A hA (extendIsometry hTH u), h₀]
    with p hl hu hr he
  change extend hTH (eventProcess F μ T s A hA u) p =
    eventProcess F μ H s A hA (extendIsometry hTH u) p
  rw [hl, hr]
  by_cases hb : p ∈ before (T : ℝ)
  · rw [indicator_of_mem hb, he hb]
    by_cases ha : p ∈ eventAfter s A
    · rw [indicator_of_mem ha, indicator_of_mem ha]
      exact (hu.trans (indicator_of_mem hb _)).symm
    · simp [indicator_of_notMem ha]
  · rw [indicator_of_notMem hb]
    by_cases ha : p ∈ eventAfter s A
    · rw [indicator_of_mem ha]
      change 0 = extend hTH u p
      rw [hu, indicator_of_notMem hb]
    · rw [indicator_of_notMem ha]

theorem restrictTerminal_locality (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (hTH : T ≤ H) :
    StandardTerminalPastLocality (restrictTerminal J hTH) := by
  intro s A hA u
  change J.integral (extendIsometry hTH (eventProcess F μ T s A hA u)) =ᵐ[μ]
    A.indicator (J.integral (extendIsometry hTH (post F μ T s u)))
  have hp : extendIsometry hTH (post F μ T s u) = post F μ H s (extendIsometry hTH u) :=
    extend_eventProcess hTH s univ MeasurableSet.univ u
  rw [extend_eventProcess, hp]
  exact hJ s A hA (extendIsometry hTH u)

theorem restrictTerminal_representation (J : StandardTerminalIto (C := C) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (hTH : T ≤ H) (X : Lp E 2 μ)
    (hX : AEStronglyMeasurable[F T] (X : Ω → E) μ)
    (hrep : ∃ v : Process (E := C) F μ H, J.integral v = X) :
    ∃ u : Process (E := C) F μ T, (restrictTerminal J hTH).integral u = X :=
  restrict_representation J hJ hTH X hX hrep

private theorem extend_stop_shorten (hTH : T ≤ H) {s : ℝ≥0} (hs : s ≤ T)
    (u : Process (E := C) F μ H) :
    extendIsometry hTH (stop F μ T s (shorten hTH u)) = stop F μ H s u := by
  have hsmall : stop F μ T s (shorten hTH u) =ᵐ[energyMeasure μ T] (before (s : ℝ)).indicator u := by
    filter_upwards [stop_ae F μ T s (shorten hTH u), ae_eq_of_ae_eq_trim (shorten_ae hTH u)]
      with p hstop hu
    rw [hstop]
    by_cases hp : p ∈ before (s : ℝ)
    · simpa only [indicator_of_mem hp] using hu
    · simp only [indicator_of_notMem hp]
  have hsmall' := (ae_restrict_iff' ((predictable_le_product F) _ (before_measurable F T))).mp
    (show stop F μ T s (shorten hTH u) =ᵐ[(energyMeasure μ H).restrict (before (T : ℝ))]
      (before (s : ℝ)).indicator u by rw [restrict_energy μ hTH]; exact hsmall)
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [ae_eq_of_ae_eq_trim (extend_ae hTH (stop F μ T s (shorten hTH u))), hsmall',
    stop_ae F μ H s u] with p he hsmall hstop
  change extend hTH (stop F μ T s (shorten hTH u)) p = stop F μ H s u p
  rw [he, hstop]
  by_cases hp : p ∈ before (T : ℝ)
  · rw [indicator_of_mem hp, hsmall hp]
  · have hps : p ∉ before (s : ℝ) := fun hps => hp (hps.trans_le (NNReal.coe_le_coe.mpr hs))
    simp only [indicator_of_notMem hp, indicator_of_notMem hps]

/-- The expected squared-norm Itô identity at every deterministic prefix,
with the quadratic term integrated in time on actual noise slices. -/
theorem energy_prefix [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (J : StandardTerminalIto (C := E) (E := E) F μ H)
    (hJ : StandardTerminalPastLocality J) (hTH : T ≤ H)
    (x₀ : Lp E 2 μ) (hx₀ : AEStronglyMeasurable[F 0] (x₀ : Ω → E) μ)
    (f : ℝ≥0 → Lp E 2 μ) (hf : Integrable f (timeMeasure H))
    (ha : ∀ᵐ s ∂timeMeasure H, AEStronglyMeasurable[F s] (f s : Ω → E) μ)
    (u : Process (E := E) F μ H) (Y Z : ℝ≥0 → Lp E 2 μ)
    (hZ : ∀ᵐ s ∂timeMeasure H, (fun ω => u (s, ω)) =ᵐ[μ] Z s)
    (hY : ∀ s, s ≤ H → Y s =
      x₀ + HeatDeterministicPairing.cumulative (timeMeasure H) f s + HeatStoppedPairing.value F μ H J u s) :
    ‖Y T‖ ^ 2 - ‖x₀‖ ^ 2 =
      2 * (∫ s, inner ℝ (f s) (Y s) ∂timeMeasure T) + ∫ s, ‖Z s‖ ^ 2 ∂timeMeasure T := by
  let I := restrictTerminal J hTH
  let v := shorten hTH u
  have hd (s : ℝ≥0) (hs : s ≤ T) :
      HeatDeterministicPairing.cumulative (timeMeasure T) f s =
        HeatDeterministicPairing.cumulative (timeMeasure H) f s := by
    unfold HeatDeterministicPairing.cumulative
    rw [HeatTimeRestriction.restrict_Iio hs, HeatTimeRestriction.restrict_Iio (hs.trans hTH)]
  have hi (s : ℝ≥0) (hs : s ≤ T) :
      HeatStoppedPairing.value F μ T I v s = HeatStoppedPairing.value F μ H J u s := by
    change J.integral (extendIsometry hTH (stop F μ T s v)) = J.integral (stop F μ H s u)
    rw [extend_stop_shorten hTH hs u]
  have h := HeatItoNormEnergy.energy F μ T I (restrictTerminal_locality J hJ hTH)
    x₀ hx₀ f (hf.mono_measure (HeatTimeRestriction.mono hTH)) (ae_mono (HeatTimeRestriction.mono hTH) ha)
    v Y (fun s hs => by rw [hd s hs, hi s hs]; exact hY s (hs.trans hTH))
  have he : extendIsometry hTH (stop F μ T T v) = stop F μ H T u := extend_stop_shorten hTH le_rfl u
  rw [← (extendIsometry hTH).norm_map (stop F μ T T v), he,
    HeatStoppedSliceEnergy.energy F μ H u Z hZ hTH] at h
  exact h

end HeatTerminalItoCompression

#print axioms HeatTerminalItoCompression.extend_shorten_eq_stop
#print axioms HeatTerminalItoCompression.restrict_representation
#print axioms HeatTerminalItoCompression.restrictTerminal_locality
#print axioms HeatTerminalItoCompression.restrictTerminal_representation
#print axioms HeatTerminalItoCompression.energy_prefix
