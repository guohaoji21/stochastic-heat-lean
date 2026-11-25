import HeatControlAdapted

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatControlInjection
open MeasureTheory SHE.PredictableL2
open scoped NNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (B : C →L[ℝ] E) (U : ℝ≥0 → Ω → C) (hU : IsStronglyProgressive F U)

include hU in
theorem progressive : IsStronglyProgressive F (fun t ω => B (U t ω)) :=
  fun t => B.continuous.comp_stronglyMeasurable (hU t)

include hU in
theorem energy (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    Integrable (fun p : ℝ≥0 × Ω => ‖B (U p.1 p.2)‖^2) (energyMeasure μ H) := by
  have hp := progressive F B U hU
  have hm := HeatControlAdapted.clamp_measurable F (fun t ω => B (U t ω)) hp H
  have he : HeatControlAdapted.clamp (fun t ω => B (U t ω)) H=ᵐ[energyMeasure μ H]
      (fun p => B (U p.1 p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    simp only [HeatControlAdapted.clamp,min_eq_left hp.2]
  have hme : AEStronglyMeasurable (fun p : ℝ≥0 × Ω => B (U p.1 p.2)) (energyMeasure μ H) :=
    hm.aestronglyMeasurable.congr he
  apply (hE.const_mul (‖B‖^2)).mono' (hme.norm.pow 2)
  exact Filter.Eventually.of_forall (fun p => by
    change ‖‖B (U p.1 p.2)‖^2‖≤‖B‖^2*‖U p.1 p.2‖^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm (U p.1 p.2)) 2).trans_eq (mul_pow _ _ _))

end HeatControlInjection
#check @HeatControlInjection.progressive
#print axioms HeatControlInjection.progressive
#check @HeatControlInjection.energy
#print axioms HeatControlInjection.energy
