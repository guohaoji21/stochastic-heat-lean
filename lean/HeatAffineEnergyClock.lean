import SHE.IntervalTimeMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace HeatAffineEnergyClock

open Filter MeasureTheory Set SHE.PredictableL2
open scoped NNReal

private theorem preserve (H : ℝ≥0) :
    MeasurePreserving ((↑) : ℝ≥0 → ℝ) (timeMeasure H)
      (volume.restrict (Ioc (0 : ℝ) H)) :=
  ⟨nonnegative_coe_measurableEmbedding.measurable, timeMeasure_map H⟩

theorem integral (g : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (∫ s, g s ∂timeMeasure t) = ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal := by
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) by positivity)]
  simpa only [Real.toNNReal_coe] using
    (preserve t).integral_comp nonnegative_coe_measurableEmbedding (fun s => g s.toNNReal)

private theorem intervalIntegrable_lift (H : ℝ≥0) {g : ℝ≥0 → ℝ}
    (hg : Integrable g (timeMeasure H)) :
    IntervalIntegrable (fun s : ℝ => g s.toNNReal) volume 0 (H : ℝ) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ (H : ℝ) by positivity)]
  exact ((preserve H).integrable_comp_emb nonnegative_coe_measurableEmbedding).mp
    (by simpa only [Function.comp_def, Real.toNNReal_coe] using hg)

private theorem ac_finset_sum {κ : Type*} (S : Finset κ) (f : κ → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ k ∈ S, AbsolutelyContinuousOnInterval (f k) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ k ∈ S, f k t) a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
  | @insert k S hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k (Finset.mem_insert_self _ _)).fun_add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- An affine exponential weight can be inserted into a finite family of
expected energy primitives. The local sign of the compensated density
compares the weighted endpoint energies on the original nonnegative clock. -/
theorem endpoint_le {κ : Type*} [Fintype κ] {H a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H)
    (c r : κ → ℝ) (f g : κ → ℝ≥0 → ℝ)
    (hg : ∀ k, Integrable (g k) (timeMeasure H))
    (hf : ∀ k t, t ≤ H → f k t = f k 0 + ∫ s, g k s ∂timeMeasure t)
    (hnonneg : ∀ᵐ t ∂timeMeasure H, t ∈ Ioc a b →
      0 ≤ ∑ k, Real.exp (c k + r k * (t : ℝ)) * (g k t + r k * f k t)) :
    (∑ k, Real.exp (c k + r k * (a : ℝ)) * f k a) ≤
      ∑ k, Real.exp (c k + r k * (b : ℝ)) * f k b := by
  let fR (k : κ) (t : ℝ) := f k 0 + ∫ s in (0 : ℝ)..t, g k s.toNNReal
  let W (t : ℝ) := ∑ k, Real.exp (c k + r k * t) * fR k t
  have him (k : κ) : IntervalIntegrable (fun s : ℝ => g k s.toNNReal) volume 0 (H : ℝ) :=
    intervalIntegrable_lift H (hg k)
  have hEq (k : κ) {t : ℝ≥0} (ht : t ≤ H) : fR k t = f k t := by
    rw [hf k t ht, integral]
  have hAC (k : κ) : AbsolutelyContinuousOnInterval (fR k) 0 (H : ℝ) :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => f k 0)).contDiffOn.absolutelyContinuousOnInterval).fun_add
      ((him k).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp))
  have hWAC : AbsolutelyContinuousOnInterval W 0 (H : ℝ) := by
    apply ac_finset_sum
    intro k _
    have hc : ContDiff ℝ 1 (fun s : ℝ => Real.exp (c k + r k * s)) := by fun_prop
    exact hc.contDiffOn.absolutelyContinuousOnInterval.fun_mul (hAC k)
  have hWab : AbsolutelyContinuousOnInterval W (a : ℝ) (b : ℝ) :=
    hWAC.mono (by
      rw [uIcc_of_le (show (a : ℝ) ≤ b by exact_mod_cast hab),
        uIcc_of_le (show (0 : ℝ) ≤ (H : ℝ) by positivity)]
      exact Icc_subset_Icc a.property (by exact_mod_cast hbH))
  have hpres : MeasurePreserving ((↑) : ℝ≥0 → ℝ) ((timeMeasure H).restrict (Ioc a b))
      (volume.restrict (Ioc (a : ℝ) (b : ℝ))) := by
    refine ⟨nonnegative_coe_measurableEmbedding.measurable, ?_⟩
    rw [timeMeasure_restrict_Ioc a hbH, intervalTimeMeasure_map]
  have hpos : ∀ᵐ t ∂(volume.restrict (Ioc (a : ℝ) (b : ℝ))),
      0 ≤ ∑ k, Real.exp (c k + r k * t) * (g k t.toNNReal + r k * f k t.toNNReal) := by
    rw [← hpres.map_eq, nonnegative_coe_measurableEmbedding.ae_map_iff]
    have hh := (ae_restrict_iff' measurableSet_Ioc).mpr hnonneg
    simpa only [Real.toNNReal_coe] using hh
  have hderiv : ∀ᵐ t : ℝ ∂volume, t ∈ uIcc 0 (H : ℝ) → ∀ k,
      HasDerivAt (fR k) (g k t.toNNReal) t := by
    filter_upwards [ae_all_iff.mpr (fun k => (him k).ae_hasDerivAt_integral)] with t ht
    intro htH k
    exact (ht k htH 0 (by simp)).const_add (f k 0)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hnon : ∀ᵐ t ∂(volume.restrict (Ioc (a : ℝ) (b : ℝ))), 0 ≤ deriv W t := by
    filter_upwards [hpos, ae_mono Measure.restrict_le_self hderiv,
      ae_restrict_mem measurableSet_Ioc] with t htpos hdt htab
    have ht0 : 0 ≤ t := a.property.trans htab.1.le
    have htH : t ≤ H := htab.2.trans (by exact_mod_cast hbH)
    have hNN : t.toNNReal ≤ H := by
      exact_mod_cast (show (t.toNNReal : ℝ) ≤ H by rwa [Real.coe_toNNReal _ ht0])
    have heq (k : κ) : fR k t = f k t.toNNReal := by
      simpa only [Real.coe_toNNReal _ ht0] using hEq k hNN
    have hd : HasDerivAt W
        (∑ k, Real.exp (c k + r k * t) * (g k t.toNNReal + r k * f k t.toNNReal)) t := by
      apply HasDerivAt.fun_sum
      intro k _
      have hx : HasDerivAt (fun x : ℝ => c k + r k * x) (r k) t := by
        have hlin : HasDerivAt (fun x : ℝ => r k * x) (r k) t := by
          simpa only [mul_one] using (hasDerivAt_id' t).const_mul (r k)
        exact hlin.const_add (c k)
      have hmem : t ∈ uIcc 0 (H : ℝ) := by
        rw [uIcc_of_le (show (0 : ℝ) ≤ (H : ℝ) by positivity)]
        exact ⟨ht0, htH⟩
      have h := hx.exp.mul (hdt hmem k)
      convert h using 1
      rw [heq k]
      ring
    rw [hd.deriv]
    exact htpos
  have hin : 0 ≤ ∫ s in (a : ℝ)..(b : ℝ), deriv W s := by
    rw [intervalIntegral.integral_of_le habR]
    exact integral_nonneg_of_ae hnon
  rw [hWab.integral_deriv_eq_sub] at hin
  simpa only [W, hEq _ (hab.trans hbH), hEq _ hbH] using sub_nonneg.mp hin

end HeatAffineEnergyClock

#print axioms HeatAffineEnergyClock.endpoint_le
