import HeatFourierFrameMeasure
import HeatScalarControlBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatModalControlEnergy
open MeasureTheory Filter SHE.PredictableL2 HeatIntervalNormalization HeatFourierFrame
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (f : ℝ≥0 × Ω → Base) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))

def bound (n : ℤ) : Ω → ℝ := HeatScalarControlBound.bound H (fun p => coordinate n (f p))

include hfm in
theorem square_integrable (n : ℤ) : MemLp (bound H f n) 2 μ :=
  HeatScalarControlBound.square_integrable μ H _ ((coordinate n).comp_memLp' hfm)

include hf hfm in
theorem energy :
    (∑' n : ℤ,∫⁻ ω,ENNReal.ofReal ((bound H f n ω)^2) ∂μ)=
      ENNReal.ofReal (H:ℝ)*(∫⁻ p,ENNReal.ofReal (‖f p‖^2) ∂energyMeasure μ H) := by
  have he (n : ℤ) : (∫⁻ ω,ENNReal.ofReal ((bound H f n ω)^2) ∂μ)=
      ENNReal.ofReal (H:ℝ)*(∫⁻ p,ENNReal.ofReal ((coordinate n (f p))^2) ∂energyMeasure μ H) := by
    have hm : MemLp (fun p => coordinate n (f p)) 2 (energyMeasure μ H) := by
      simpa only [Function.comp_def] using (coordinate n).comp_memLp' hfm
    have hi : Integrable (fun p => (coordinate n (f p))^2) (energyMeasure μ H) := by
      simpa only [Real.norm_eq_abs,sq_abs] using hm.norm.integrable_sq
    rw [←ofReal_integral_eq_lintegral_ofReal (square_integrable μ H f hfm n).integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _))]
    change ENNReal.ofReal (∫ ω,(HeatScalarControlBound.bound H (fun p => coordinate n (f p)) ω)^2 ∂μ)=_
    rw [HeatScalarControlBound.energy μ H _ hm]
    calc
      _ = ENNReal.ofReal (H:ℝ)*ENNReal.ofReal (∫ p,(coordinate n (f p))^2 ∂energyMeasure μ H) :=
        ENNReal.ofReal_mul H.property
      _ = _ := congrArg (fun z => ENNReal.ofReal (H:ℝ)*z)
        (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)))
  simp_rw [he]
  rw [ENNReal.tsum_mul_left,HeatFourierFrameMeasure.integrated_parseval (energyMeasure μ H) f hf]

include hf hfm in
theorem finite : (∑' n : ℤ,∫⁻ ω,ENNReal.ofReal ((bound H f n ω)^2) ∂μ)<∞ := by
  rw [energy μ H f hf hfm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hfm.norm.integrable_sq.2)

end HeatModalControlEnergy
#check @HeatModalControlEnergy.square_integrable
#print axioms HeatModalControlEnergy.square_integrable
#check @HeatModalControlEnergy.energy
#print axioms HeatModalControlEnergy.energy
#check @HeatModalControlEnergy.finite
#print HeatModalControlEnergy.finite
#print axioms HeatModalControlEnergy.finite
