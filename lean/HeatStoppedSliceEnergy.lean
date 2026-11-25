import HeatSliceEnergy
import HeatTimeRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatStoppedSliceEnergy
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (u : Process (E := E) F μ H) (V : ℝ≥0 → Lp E 2 μ)
  (hV : ∀ᵐ t ∂timeMeasure H,(fun ω => u (t,ω))=ᵐ[μ] V t)

include hV in
theorem energy {T : ℝ≥0} (hT : T ≤ H) :
    ‖StoppedItoInputs.stop F μ H T u‖^2=∫ t,‖V t‖^2 ∂timeMeasure T := by
  have hu : Integrable (fun p => ‖u p‖^2) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  have hslice : (fun t => ‖V t‖^2)=ᵐ[timeMeasure H] fun t => ∫ ω,‖u (t,ω)‖^2 ∂μ := by
    filter_upwards [hV] with t ht
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ht] with ω hω
    rw [hω,real_inner_self_eq_norm_sq]
  let f := fun p : ℝ≥0 × Ω => ((Iio T).indicator (fun s => ‖u (s,p.2)‖^2)) p.1
  have hfi : Integrable f (energyMeasure μ H) :=
    hu.indicator ((measurableSet_Iio : MeasurableSet (Iio T : Set ℝ≥0)).preimage measurable_fst)
  have he : (fun p : ℝ≥0 × Ω => ‖StoppedItoInputs.stop F μ H T u p‖^2)=ᵐ[energyMeasure μ H] f := by
    filter_upwards [StoppedItoInputs.stop_ae F μ H T u] with p hp
    rw [hp]
    by_cases hs : p.1<T
    · have hmem : p∈StoppedItoInputs.before (T:ℝ) := by exact_mod_cast hs
      rw [Set.indicator_of_mem hmem]
      exact (Set.indicator_of_mem (show p.1∈Iio T from hs) (fun s => ‖u (s,p.2)‖^2)).symm
    · have hmem : p∉StoppedItoInputs.before (T:ℝ) := by exact_mod_cast hs
      rw [Set.indicator_of_notMem hmem,norm_zero,zero_pow (by norm_num : 2≠0)]
      exact (Set.indicator_of_notMem (show p.1∉Iio T from hs) (fun s => ‖u (s,p.2)‖^2)).symm
  rw [subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F),integral_congr_ae he]
  have hprod : (∫ p,f p ∂energyMeasure μ H)=∫ t,∫ ω,f (t,ω) ∂μ ∂timeMeasure H := integral_prod f hfi
  rw [hprod]
  have hinner : (fun t => ∫ ω,f (t,ω) ∂μ)=
      (Iio T).indicator (fun t => ∫ ω,‖u (t,ω)‖^2 ∂μ) := by
    funext t
    by_cases ht : t<T
    · have heq : (fun ω => f (t,ω))=fun ω => ‖u (t,ω)‖^2 :=
        funext fun ω => Set.indicator_of_mem (show t∈Iio T from ht) _
      rw [heq,Set.indicator_of_mem (show t∈Iio T from ht)]
    · have heq : (fun ω => f (t,ω))=fun _ => (0:ℝ) :=
        funext fun ω => Set.indicator_of_notMem (show t∉Iio T from ht) _
      rw [heq,integral_zero,Set.indicator_of_notMem (show t∉Iio T from ht)]
  rw [hinner,integral_indicator measurableSet_Iio]
  have htmeasure := HeatTimeRestriction.restrict_Iio hT
  rw [htmeasure]
  apply integral_congr_ae
  filter_upwards [ae_mono (HeatTimeRestriction.mono hT) hslice] with t ht
  exact ht.symm

end HeatStoppedSliceEnergy
#check @HeatStoppedSliceEnergy.energy
#print axioms HeatStoppedSliceEnergy.energy
