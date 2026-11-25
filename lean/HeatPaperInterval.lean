import HeatPaperMain
import HeatIntervalObservability
import HeatIntervalPaperDaviesGaffney

set_option autoImplicit false
noncomputable section

namespace HeatPaperInterval

open MeasureTheory Set Filter HeatIntervalNormalization HeatCanonicalPredictableSolution
open scoped ENNReal

/-- Multiplication by the paper's coefficient sends the first Dirichlet
sine mode outside its one-dimensional span. -/
theorem first_mode_not_invariant (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖b x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂baseMeasure, x ∉ Ioo (6 : ℝ) 7 → b x = 0)
    (hplateau : ∀ x ∈ Ioo (25/4 : ℝ) (27/4), b x = 1) (scale : ℝ) :
    let f := HeatSineH01.sine (Real.pi / 10)
    noise b hb hbound f ≠ scale • f := by
  let f := HeatSineH01.sine (Real.pi / 10)
  change noise b hb hbound f ≠ scale • f
  intro heq
  have hb_ae := SHEStochastic.BoundedFieldOperator.operator_ae (HeatScalarMultiplier.field baseMeasure b hb hbound) f
  have hf : (f : ℝ → ℝ) =ᵐ[baseMeasure] fun x => Real.sin (Real.pi / 10 * x) :=
    HeatSineH01.sine_ae _
  have hconstant : ∀ᵐ x ∂baseMeasure, x ∈ Ioo (0 : ℝ) 10 → b x = scale := by
    filter_upwards [hb_ae, hf, Lp.coeFn_smul scale f] with x hb₀ hf₀ hscaled hx
    change noise b hb hbound f x = b x * f x at hb₀
    rw [heq, hscaled, Pi.smul_apply, smul_eq_mul, hf₀] at hb₀
    have hangle : Real.pi / 10 * x < Real.pi := by
      calc
        _ < Real.pi / 10 * 10 := mul_lt_mul_of_pos_left hx.2 (by positivity)
        _ = _ := by ring
    have hs := Real.sin_pos_of_pos_of_lt_pi (mul_pos (by positivity) hx.1) hangle
    exact (mul_right_cancel₀ hs.ne' hb₀).symm
  have hselect {a d : ℝ} {Q : ℝ → Prop} (had : a < d) (hin : Ioo a d ⊆ Ioo (0 : ℝ) 10)
      (hgood : ∀ᵐ x ∂baseMeasure, x ∈ Ioo a d → Q x) : ∃ x ∈ Ioo a d, Q x := by
    by_contra! hn
    have hbad : ∀ᵐ x ∂baseMeasure, x ∉ Ioo a d := by
      filter_upwards [hgood] with x hx hxmem
      exact hn x hxmem (hx hxmem)
    have hm : baseMeasure (Ioo a d) = 0 := by
      simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hbad
    rw [baseMeasure, Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hin, Real.volume_Ioo] at hm
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr had)).ne' hm
  have hz : scale = 0 := by
    have hout : ∀ᵐ x ∂baseMeasure, x ∈ Ioo (1 : ℝ) 2 → b x = scale ∧ b x = 0 := by
      filter_upwards [hconstant, hsupp] with x h₁ h₂ hx
      exact ⟨h₁ ⟨by linarith [hx.1], by linarith [hx.2]⟩, h₂ (fun hy => by linarith [hx.2, hy.1])⟩
    have hin : Ioo (1 : ℝ) 2 ⊆ Ioo (0 : ℝ) 10 := Ioo_subset_Ioo (by norm_num) (by norm_num)
    obtain ⟨_, _, hscale, hzero⟩ := hselect (by norm_num) hin hout
    exact hscale.symm.trans hzero
  have hin : Ioo (25/4 : ℝ) (27/4) ⊆ Ioo (0 : ℝ) 10 := Ioo_subset_Ioo (by norm_num) (by norm_num)
  obtain ⟨x, hx, hbscale⟩ := hselect (by norm_num) hin (hconstant.mono fun _ h hmem => h (hin hmem))
  rw [hplateau x hx, hz] at hbscale
  norm_num at hbscale

end HeatPaperInterval

#print axioms HeatPaperInterval.first_mode_not_invariant
