import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace HeatConditionalFubini
open MeasureTheory Filter
open scoped NNReal


variable {X Ω E : Type*} [MeasurableSpace X] [m0 : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (ν : Measure X) [SFinite ν] (μ : Measure Ω) [IsFiniteMeasure μ]
  (F : Filtration ℝ≥0 m0) (a : ℝ≥0)


include F a in
theorem conditional_integral (f g : X × Ω → E)
    (hf : Integrable f (ν.prod μ)) (hg : Integrable g (ν.prod μ))
    (hG : AEStronglyMeasurable[F a] (fun ω => ∫ s, g (s,ω) ∂ν) μ)
    (hfg : ∀ᵐ s ∂ν, μ[(fun ω => f (s,ω)) | F a] =ᵐ[μ] (fun ω => g (s,ω))) :
    μ[(fun ω => ∫ s, f (s,ω) ∂ν) | F a] =ᵐ[μ] (fun ω => ∫ s, g (s,ω) ∂ν) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le a) hf.integral_prod_right
    (fun A _ _ => hg.integral_prod_right.integrableOn) (fun A hA _ => ?_) hG).symm
  have hfA : Integrable f (ν.prod (μ.restrict A)) :=
    hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hgA : Integrable g (ν.prod (μ.restrict A)) :=
    hg.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ ω in A, (∫ s, g (s,ω) ∂ν) ∂μ) = ∫ s, (∫ ω in A, g (s,ω) ∂μ) ∂ν :=
      (integral_integral_swap (f := fun s ω => g (s,ω)) hgA).symm
    _ = ∫ s, (∫ ω in A, f (s,ω) ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hfg,hf.prod_right_ae] with s hs hi
      calc
        _ = ∫ ω in A, μ[(fun ω => f (s,ω)) | F a] ω ∂μ :=
          integral_congr_ae (ae_restrict_of_ae hs.symm)
        _ = _ := setIntegral_condExp (F.le a) hi hA
    _ = ∫ ω in A, (∫ s, f (s,ω) ∂ν) ∂μ := integral_integral_swap (f := fun s ω => f (s,ω)) hfA

end HeatConditionalFubini
#check @HeatConditionalFubini.conditional_integral
#print HeatConditionalFubini.conditional_integral
#print axioms HeatConditionalFubini.conditional_integral
