import HeatTorusGaussian

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatTorusSubeigen

open MeasureTheory Set UnitAddTorus HeatTorusFourier HeatTorusReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι]

/-- Fourier characterization of the right generator on the real heat space. -/
theorem generator_iff_coefficients (P : ℝ) (f g : RealState ι) :
    HasDerivWithinAt (fun t : ℝ => realHeat P t f) g (Ici 0) 0 ↔
    ∀ k, mFourierCoeff (embed g) k =
      (↑(-frequencySquared P k) : ℂ) * mFourierCoeff (embed f) k := by
  rw [← HeatTorusFourier.generator_iff_coefficients P (embed f) (embed g)]
  constructor
  · intro hg
    simpa only [Function.comp_def, embed_realHeat] using
      (embed (ι := ι)).hasFDerivAt.comp_hasDerivWithinAt 0 hg
  · intro hg
    change HasDerivWithinAt (fun t : ℝ => realPart (heat P t (embed f))) g (Ici 0) 0
    simpa only [Function.comp_def, realPart_embed] using
      (realPart (ι := ι)).hasFDerivAt.comp_hasDerivWithinAt 0 hg

theorem orbit_integral (P : ℝ) (f g : RealState ι)
    (hg : HasDerivWithinAt (fun s : ℝ => realHeat P s f) g (Ici 0) 0)
    (t : ℝ) (ht : 0 ≤ t) :
    realHeat P t f - f = ∫ s in (0 : ℝ)..t, realHeat P s g := by
  have he := HeatTorusFourier.orbit_integral P (embed f) (embed g)
    ((generator_iff_coefficients P f g).mp hg) t ht
  have hr := congrArg (realPart (ι := ι)) he
  rw [map_sub, realPart_embed, ← realPart.intervalIntegral_comp_comm
    ((continuous_heat P (embed g)).intervalIntegrable 0 t)] at hr
  exact hr

/-- The orbit with the exponential weight has a nonnegative derivative when
the generator plus the scalar shift is nonnegative. -/
theorem shifted_orbit_integral (P C : ℝ) (f g : RealState ι)
    (hg : HasDerivWithinAt (fun s : ℝ => realHeat P s f) g (Ici 0) 0)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (C * t) • realHeat P t f - f =
      ∫ s in (0 : ℝ)..t, Real.exp (C * s) • realHeat P s (g + C • f) := by
  have he : Continuous (fun s : ℝ => Real.exp (C * s)) := by fun_prop
  have hf := continuous_realHeat P f
  have hw : Continuous (fun s : ℝ => Real.exp (C * s) • realHeat P s (g + C • f)) :=
    he.smul (continuous_realHeat P (g + C • f))
  have hcont : Continuous (fun s : ℝ => Real.exp (C * s) • realHeat P s f) := he.smul hf
  have hd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) :
      HasDerivWithinAt (fun u : ℝ => Real.exp (C * u) • realHeat P u f)
        (Real.exp (C * s) • realHeat P s (g + C • f)) (Ioi s) s := by
    have hc := continuous_realHeat P g
    have hI : HasDerivAt (fun u : ℝ => ∫ v in (0 : ℝ)..u, realHeat P v g)
        (realHeat P s g) s := intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 s) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    have ho : HasDerivWithinAt (fun u : ℝ => realHeat P u f) (realHeat P s g) (Ici 0) s := by
      apply (hI.add_const f).hasDerivWithinAt.congr_of_mem _ (show s ∈ Ici (0 : ℝ) from hs.1.le)
      intro u hu
      exact sub_eq_iff_eq_add.mp (orbit_integral P f g hg u hu)
    have hx : HasDerivAt (fun u : ℝ => Real.exp (C * u)) (Real.exp (C * s) * C) s := by
      simpa only [Function.comp_def, id_eq, mul_one] using
        (Real.hasDerivAt_exp (C * s)).comp s ((hasDerivAt_id s).const_mul C)
    have hp := hx.hasDerivWithinAt.smul (ho.mono (show Ioi s ⊆ Ici (0 : ℝ) from
      fun _ hu => (hs.1.trans hu).le))
    change HasDerivWithinAt (fun u : ℝ => Real.exp (C * u) • realHeat P u f) _ (Ioi s) s at hp
    simpa only [map_add, map_smul, smul_add, smul_smul] using hp
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    hcont.continuousOn hd (hw.intervalIntegrable 0 t)
  simpa only [mul_zero, Real.exp_zero, one_smul, realHeat_zero, ContinuousLinearMap.id_apply]
    using h.symm

/-- A real generator subeigenvector gives an almost-everywhere heat lower bound. -/
theorem heat_lower (P C : ℝ) (f g : RealState ι)
    (hg : HasDerivWithinAt (fun s : ℝ => realHeat P s f) g (Ici 0) 0)
    (hpos : ∀ᵐ x ∂volume, 0 ≤ (g + C • f) x) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ x ∂volume, (Real.exp (-C * t) • f) x ≤ realHeat P t f x := by
  let F := fun s : ℝ => Real.exp (C * s) • realHeat P s (g + C • f)
  have hF : Continuous F := (by fun_prop : Continuous (fun s : ℝ => Real.exp (C * s))).smul
    (continuous_realHeat P _)
  have hI : Integrable F ((volume : Measure ℝ).restrict (Ioc 0 t)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (hF.intervalIntegrable 0 t)
  have hnn (s : ℝ) : ∀ᵐ x ∂volume, 0 ≤ F s x := by
    filter_upwards [HeatTorusGaussian.realHeat_nonnegative P s _ hpos,
      Lp.coeFn_smul (Real.exp (C * s)) (realHeat P s (g + C • f))] with x hx he
    change 0 ≤ (Real.exp (C * s) • realHeat P s (g + C • f)) x
    rw [he]
    exact mul_nonneg (Real.exp_pos _).le hx
  have hp := HeatTorusGaussian.integral_nonnegative (volume.restrict (Ioc 0 t)) F hI
    (Filter.Eventually.of_forall hnn)
  have he : (∫ s, F s ∂volume.restrict (Ioc 0 t)) =
      Real.exp (C * t) • realHeat P t f - f := by
    rw [shifted_orbit_integral P C f g hg t ht, intervalIntegral.integral_of_le ht]
  rw [he] at hp
  filter_upwards [hp, Lp.coeFn_sub (Real.exp (C * t) • realHeat P t f) f,
    Lp.coeFn_smul (Real.exp (C * t)) (realHeat P t f),
    Lp.coeFn_smul (Real.exp (-C * t)) f] with x hx hsub hheat hf
  rw [hsub] at hx
  change 0 ≤ (Real.exp (C * t) • realHeat P t f) x - f x at hx
  rw [hheat] at hx
  rw [hf]
  change Real.exp (-C * t) * f x ≤ realHeat P t f x
  have h := mul_le_mul_of_nonneg_left (sub_nonneg.mp hx) (Real.exp_pos (-C * t)).le
  change Real.exp (-C * t) * f x ≤ Real.exp (-C * t) *
    (Real.exp (C * t) * realHeat P t f x) at h
  rwa [← mul_assoc, ← Real.exp_add, show -C * t + C * t = 0 by ring, Real.exp_zero, one_mul] at h

end HeatTorusSubeigen

#print axioms HeatTorusSubeigen.generator_iff_coefficients
#print axioms HeatTorusSubeigen.shifted_orbit_integral
#print axioms HeatTorusSubeigen.heat_lower
