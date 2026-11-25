import HeatMomentAlgebra
import SHE.PredictableExponential

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatMomentUnweight
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem uniform (γ : ℝ) (hγ : 0≤γ) (D : ℝ) (u : Process (E := E) F μ H)
    (hu : u∈HeatMomentBall.Ball D) :
    ∀ᵐ t ∂timeMeasure H, HeatMomentBall.moment (μ:=μ)
      (fun ω => PredictableExponential.scale F μ H γ u (t,ω))≤ENNReal.ofReal (Real.exp (16*γ*(H:ℝ))*D) := by
  have hm : Measurable (u : ℝ≥0 × Ω → E) :=
    ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
  filter_upwards [Measure.ae_ae_of_ae_prod (PredictableExponential.ae F μ H γ u),hu,
    timeMeasure_ae_mem H] with t ht hu htime
  rw [HeatMomentBall.moment_congr ht]
  change HeatMomentBall.moment (μ:=μ) (fun ω => Real.exp (γ*min (t:ℝ) (H:ℝ)) • u (t,ω))≤_
  rw [min_eq_left (show (t:ℝ)≤H from by exact_mod_cast htime.2)]
  have hs : Measurable (fun ω => u (t,ω)) := hm.comp (measurable_const.prodMk measurable_id)
  rw [HeatMomentAlgebra.smul μ (fun ω => u (t,ω)) hs]
  have he : |Real.exp (γ*(t:ℝ))|^16≤Real.exp (16*γ*(H:ℝ)) := by
    rw [abs_of_pos (Real.exp_pos _),←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have htt : (t:ℝ)≤H := by exact_mod_cast htime.2
    nlinarith only [mul_le_mul_of_nonneg_left htt hγ]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (16*γ*(H:ℝ)))*ENNReal.ofReal D :=
      mul_le_mul (ENNReal.ofReal_le_ofReal he) hu bot_le bot_le
    _ = _ := (ENNReal.ofReal_mul (Real.exp_nonneg _) : ENNReal.ofReal (Real.exp (16*γ*(H:ℝ))*D)=_).symm

end HeatMomentUnweight
#check @HeatMomentUnweight.uniform
#print axioms HeatMomentUnweight.uniform
