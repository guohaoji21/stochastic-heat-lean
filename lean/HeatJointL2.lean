import HeatControlConvolution

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatJointL2
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem of_fibre_bound (f : ℝ≥0 × Ω → E) (hf : Measurable f)
    (hfm : ∀ s, MemLp (fun ω => f (s,ω)) 2 μ)
    (B : ℝ) (hB : ∀ s, (∫ ω,‖f (s,ω)‖^2 ∂μ)≤B) :
    MemLp f 2 (energyMeasure μ H) := by
  have hsq : AEStronglyMeasurable (fun p => ‖f p‖^2) (energyMeasure μ H) :=
    (hf.stronglyMeasurable.norm.pow 2).aestronglyMeasurable
  have hi : Integrable (fun s => ∫ ω,‖f (s,ω)‖^2 ∂μ) (timeMeasure H) := by
    apply (integrable_const B).mono' hsq.integral_prod_right'
    exact Eventually.of_forall (fun s => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
      exact hB s)
  apply (memLp_two_iff_integrable_sq_norm hf.stronglyMeasurable.aestronglyMeasurable).mpr
  apply (integrable_prod_iff hsq).mpr
  refine ⟨Eventually.of_forall (fun s => (hfm s).norm.integrable_sq),?_⟩
  apply hi.congr
  exact Eventually.of_forall (fun s => by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => (Real.norm_of_nonneg (sq_nonneg ‖f (s,ω)‖)).symm))

end HeatJointL2
#check @HeatJointL2.of_fibre_bound
#print HeatJointL2.of_fibre_bound
#print axioms HeatJointL2.of_fibre_bound
