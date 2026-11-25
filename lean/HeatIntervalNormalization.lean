import HeatOddSurjectivity

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatIntervalNormalization
open MeasureTheory HeatFoldProbability
open scoped NNReal ENNReal

def baseMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 10)
abbrev Base := Lp ℝ 2 baseMeasure
abbrev Normalized := Lp ℝ 2 normalizedIntervalMeasure

theorem mem_normalized (f : Base) : MemLp f 2 normalizedIntervalMeasure := by
  change MemLp f 2 (ENNReal.ofReal (1/10 : ℝ) • baseMeasure)
  exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top

def transfer (f : Base) : Normalized := (mem_normalized f).toLp f

theorem transfer_ae (f : Base) : (transfer f : ℝ → ℝ) =ᵐ[normalizedIntervalMeasure] f :=
  (mem_normalized f).coeFn_toLp

theorem realLp_norm_sq {X : Type*} [MeasurableSpace X] {ν : Measure X} (f : Lp ℝ 2 ν) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂ν := by
  simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) f f)

theorem transfer_norm_sq (f : Base) : ‖transfer f‖^2 = (1/10 : ℝ) * ‖f‖^2 := by
  rw [realLp_norm_sq, realLp_norm_sq]
  have he : (∫ x, ‖transfer f x‖^2 ∂normalizedIntervalMeasure) =
      ∫ x, ‖f x‖^2 ∂normalizedIntervalMeasure := by
    exact integral_congr_ae ((transfer_ae f).mono fun _ hx => by simpa only [hx])
  rw [he]
  change (∫ x, ‖f x‖^2 ∂(ENNReal.ofReal (1/10 : ℝ) • baseMeasure)) = _
  rw [integral_smul_measure]
  norm_num

def scaled (f : Base) : Normalized := Real.sqrt 10 • transfer f

theorem scaled_norm (f : Base) : ‖scaled f‖ = ‖f‖ := by
  have hs : (Real.sqrt 10)^2 = (10 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn := transfer_norm_sq f
  have hp : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg _
  have hf : 0 ≤ ‖f‖ := norm_nonneg _
  have ht : 0 ≤ ‖transfer f‖ := norm_nonneg _
  have hsq : (Real.sqrt 10 * ‖transfer f‖)^2 = ‖f‖^2 := by
    calc
      _ = (Real.sqrt 10)^2 * ‖transfer f‖^2 := by ring
      _ = ‖f‖^2 := by rw [hs, hn]; ring
  unfold scaled
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  exact (sq_eq_sq₀ (mul_nonneg hp ht) hf).mp hsq


theorem transfer_add (f g : Base) : transfer (f+g) = transfer f + transfer g := by
  apply Lp.ext
  have hadd := Measure.ae_smul_measure (Lp.coeFn_add f g) (ENNReal.ofReal (1/10 : ℝ))
  filter_upwards [transfer_ae (f+g), transfer_ae f, transfer_ae g,
    Lp.coeFn_add (transfer f) (transfer g), hadd] with x hfg hf hg ht hb
  simp only [Pi.add_apply] at ht hb
  rw [hfg, ht, hf, hg, hb]

theorem transfer_smul (r : ℝ) (f : Base) : transfer (r • f) = r • transfer f := by
  apply Lp.ext
  have hsmul := Measure.ae_smul_measure (Lp.coeFn_smul r f) (ENNReal.ofReal (1/10 : ℝ))
  filter_upwards [transfer_ae (r • f), transfer_ae f,
    Lp.coeFn_smul r (transfer f), hsmul] with x hrf hf ht hb
  simp only [Pi.smul_apply] at ht hb
  rw [hrf, ht, hf, hb]

def transferLinear : Base →ₗ[ℝ] Normalized where
  toFun := transfer
  map_add' := transfer_add
  map_smul' := transfer_smul

def scaledIsometry : Base →ₗᵢ[ℝ] Normalized where
  toLinearMap := Real.sqrt 10 • transferLinear
  norm_map' := scaled_norm

theorem scaledIsometry_apply (f : Base) : scaledIsometry f = scaled f := rfl

theorem mem_base (g : Normalized) : MemLp g 2 baseMeasure := by
  have hg := (Lp.memLp g).smul_measure (c := (10 : ℝ≥0∞)) (by norm_num)
  have he : (10 : ℝ≥0∞) • normalizedIntervalMeasure = baseMeasure := by
    unfold normalizedIntervalMeasure baseMeasure
    rw [smul_smul]
    have hc : (10 : ℝ≥0∞) * ENNReal.ofReal (1/10 : ℝ) = 1 := by
      rw [show (10 : ℝ≥0∞) = ENNReal.ofReal (10 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    rw [hc, one_smul]
  rw [he] at hg
  exact hg

def unscaledTransfer (g : Normalized) : Base := (mem_base g).toLp g

theorem transfer_unscaled (g : Normalized) : transfer (unscaledTransfer g) = g := by
  apply Lp.ext
  have ha := Measure.ae_smul_measure (mem_base g).coeFn_toLp (ENNReal.ofReal (1/10 : ℝ))
  filter_upwards [transfer_ae (unscaledTransfer g), ha] with x ht hg
  exact ht.trans hg

theorem scaledIsometry_surjective : Function.Surjective scaledIsometry := by
  intro g
  let f : Base := (Real.sqrt 10)⁻¹ • unscaledTransfer g
  refine ⟨f, ?_⟩
  rw [scaledIsometry_apply]
  unfold scaled f
  rw [transfer_smul, transfer_unscaled, smul_smul]
  have hs : Real.sqrt 10 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp [hs]

def measureEquiv : Base ≃ₗᵢ[ℝ] Normalized :=
  LinearIsometryEquiv.ofSurjective scaledIsometry scaledIsometry_surjective


/-- An actual isometric equivalence from the paper's unnormalized L2 space to
real odd L2 functions on the unit circle. -/
def paperOddEquiv : Base ≃ₗᵢ[ℝ] HeatRealOddSemigroup.oddSpace :=
  measureEquiv.trans HeatOddSurjectivity.oddEquiv

def paperHeat (t : ℝ) : Base →L[ℝ] Base :=
  paperOddEquiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((HeatRealOddSemigroup.timeScaledHeat t).comp paperOddEquiv.toLinearIsometry.toContinuousLinearMap)

theorem paperHeat_apply (t : ℝ) (f : Base) :
    paperHeat t f = paperOddEquiv.symm (HeatRealOddSemigroup.timeScaledHeat t (paperOddEquiv f)) := rfl

theorem paperHeat_zero : paperHeat 0 = ContinuousLinearMap.id ℝ Base := by
  apply ContinuousLinearMap.ext
  intro f
  rw [paperHeat_apply, HeatRealOddSemigroup.timeScaledHeat_zero]
  simp

theorem paperHeat_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    paperHeat (s+t) = (paperHeat s).comp (paperHeat t) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, paperHeat_apply,
    HeatRealOddSemigroup.timeScaledHeat_semigroup hs ht, paperOddEquiv.apply_symm_apply]

theorem paperHeat_contraction (t : ℝ) (f : Base) : ‖paperHeat t f‖ ≤ ‖f‖ := by
  rw [paperHeat_apply, paperOddEquiv.symm.norm_map, ← paperOddEquiv.norm_map f]
  exact HeatRealOddSemigroup.timeScaledHeat_contraction t (paperOddEquiv f)

theorem paperHeat_continuous (f : Base) : Continuous (fun t : ℝ => paperHeat t f) := by
  have hc := HeatRealOddSemigroup.timeScaledHeat_continuous (paperOddEquiv f)
  change Continuous (fun t : ℝ => paperOddEquiv.symm (HeatRealOddSemigroup.timeScaledHeat t (paperOddEquiv f)))
  exact paperOddEquiv.symm.continuous.comp hc

end HeatIntervalNormalization
#check @HeatIntervalNormalization.mem_normalized
#print axioms HeatIntervalNormalization.mem_normalized
#check @HeatIntervalNormalization.transfer_ae
#print axioms HeatIntervalNormalization.transfer_ae
#check @HeatIntervalNormalization.realLp_norm_sq
#print axioms HeatIntervalNormalization.realLp_norm_sq
#check @HeatIntervalNormalization.transfer_norm_sq
#print axioms HeatIntervalNormalization.transfer_norm_sq
#check @HeatIntervalNormalization.scaled_norm
#print axioms HeatIntervalNormalization.scaled_norm

#check @HeatIntervalNormalization.transfer_add
#print axioms HeatIntervalNormalization.transfer_add
#check @HeatIntervalNormalization.transfer_smul
#print axioms HeatIntervalNormalization.transfer_smul
#check @HeatIntervalNormalization.scaledIsometry_apply
#print axioms HeatIntervalNormalization.scaledIsometry_apply
#check @HeatIntervalNormalization.mem_base
#print axioms HeatIntervalNormalization.mem_base
#check @HeatIntervalNormalization.transfer_unscaled
#print axioms HeatIntervalNormalization.transfer_unscaled
#check @HeatIntervalNormalization.scaledIsometry_surjective
#print axioms HeatIntervalNormalization.scaledIsometry_surjective

#check @HeatIntervalNormalization.paperHeat_apply
#print axioms HeatIntervalNormalization.paperHeat_apply
#check @HeatIntervalNormalization.paperHeat_zero
#print axioms HeatIntervalNormalization.paperHeat_zero
#check @HeatIntervalNormalization.paperHeat_semigroup
#print axioms HeatIntervalNormalization.paperHeat_semigroup
#check @HeatIntervalNormalization.paperHeat_contraction
#print axioms HeatIntervalNormalization.paperHeat_contraction
#check @HeatIntervalNormalization.paperHeat_continuous
#print axioms HeatIntervalNormalization.paperHeat_continuous
