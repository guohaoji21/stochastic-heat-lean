import HeatMomentBall

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatMomentAlgebra
open MeasureTheory HeatMomentBall
open scoped ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem add_bound (U V : Ω → E) (hU : Measurable U) (hV : Measurable V) :
    moment (μ:=μ) (fun ω => U ω+V ω) ≤
      ENNReal.ofReal ((2:ℝ)^15)*(moment (μ:=μ) U+moment (μ:=μ) V) := by
  have h₁ : Measurable (fun ω => ENNReal.ofReal (‖U ω‖^16)) := (hU.norm.pow_const _).ennreal_ofReal
  have h₂ : Measurable (fun ω => ENNReal.ofReal (‖V ω‖^16)) := (hV.norm.pow_const _).ennreal_ofReal
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((2:ℝ)^15)*(ENNReal.ofReal (‖U ω‖^16)+ENNReal.ofReal (‖V ω‖^16)) ∂μ := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal (‖U ω+V ω‖^16) ≤ ENNReal.ofReal ((2:ℝ)^15)*(ENNReal.ofReal (‖U ω‖^16)+ENNReal.ofReal (‖V ω‖^16))
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _).trans
        (add_pow_le (norm_nonneg _) (norm_nonneg _) 16)
    _ = _ := by
      have hsum : Measurable (fun ω => ENNReal.ofReal (‖U ω‖^16)+ENNReal.ofReal (‖V ω‖^16)) := h₁.add h₂
      rw [lintegral_const_mul'' (ENNReal.ofReal ((2:ℝ)^15)) hsum.aemeasurable,lintegral_add_left h₁]
      rfl

theorem constant_bound (x : E) (A : ℝ) (h : ‖x‖^16≤A) :
    moment (μ:=μ) (fun _ => x) ≤ ENNReal.ofReal A := by
  unfold moment
  simp only [lintegral_const,measure_univ,mul_one]
  exact ENNReal.ofReal_le_ofReal h

theorem smul (f : Ω → E) (hf : Measurable f) (a : ℝ) :
    moment (μ:=μ) (fun ω => a • f ω)=ENNReal.ofReal (|a|^16)*moment (μ:=μ) f := by
  unfold moment
  simp_rw [norm_smul,Real.norm_eq_abs,mul_pow,ENNReal.ofReal_mul (pow_nonneg (abs_nonneg a) 16)]
  exact lintegral_const_mul'' _ ((hf.norm.pow_const (16:ℕ)).ennreal_ofReal.aemeasurable)

end HeatMomentAlgebra
#check @HeatMomentAlgebra.add_bound
#print axioms HeatMomentAlgebra.add_bound
#check @HeatMomentAlgebra.constant_bound
#print axioms HeatMomentAlgebra.constant_bound

#check @HeatMomentAlgebra.smul
#print axioms HeatMomentAlgebra.smul
