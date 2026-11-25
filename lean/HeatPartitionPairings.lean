import HeatTimePartition
import HeatForwardDrift
import HeatBackwardDriftPairing
import HeatHeatedRandomVariable
import HeatL2Integrability
import HeatSampledAdjoint
import HeatSampledLp

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatPartitionPairings
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)

theorem control_sum (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (Z : ℝ≥0 → Lp E 2 μ) (n : ℕ) :
    (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),
      inner ℝ (HeatForwardDrift.value μ H S hS hcontr f hf hfm (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k))
        (((S (HeatDualityGrid.width n)).compLpL 2 μ) (Z (HeatDualityGrid.point H n k))))=
      ∫ p,inner ℝ (f p) (HeatSampledAdjoint.raw μ H S Z n p) ∂energyMeasure μ H := by
  have hh := HeatTimePartition.integral_selected μ H n
    (fun k p => inner ℝ (f p) (S (HeatDualityGrid.width n+(HeatDualityGrid.point H n k-p.1)) (Z (HeatDualityGrid.point H n k) p.2)))
    (fun k _ => HeatL2Integrability.inner (energyMeasure μ H) _ _ hfm
      (HeatHeatedRandomVariable.square_integrable μ H S hS hcontr _
        (measurable_const.add (measurable_const.sub measurable_id)) (Z (HeatDualityGrid.point H n k))))
  calc
    _ = _ := Finset.sum_congr rfl (fun k _ => HeatForwardDrift.pairing μ H S hS hcontr hsem hsym f hf hfm _ _ _ _)
    _ = _ := hh

theorem drift_sum (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (V : ℝ≥0 → Lp E 2 μ) (v : Process (E := E) F μ H) (n : ℕ) :
    (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),
      inner ℝ (((S (HeatDualityGrid.width n)).compLpL 2 μ) (V (HeatDualityGrid.point H n (k-1))))
        (HeatActualCellEnergy.drift F μ H S hS hcontr M (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k) v))=
      ∫ p,inner ℝ (M (v p)) (HeatSampledLp.raw μ H S V n p) ∂energyMeasure μ H := by
  have hv := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  have hh := HeatTimePartition.integral_selected μ H n
    (fun k p => inner ℝ (M (v p)) (S (HeatDualityGrid.width n+(p.1-HeatDualityGrid.point H n (k-1))) (V (HeatDualityGrid.point H n (k-1)) p.2)))
    (fun k _ => HeatL2Integrability.inner (energyMeasure μ H) _ _ (M.comp_memLp' hv)
      (HeatHeatedRandomVariable.square_integrable μ H S hS hcontr _
        (measurable_const.add (measurable_id.sub measurable_const)) (V (HeatDualityGrid.point H n (k-1)))))
  calc
    _ = _ := Finset.sum_congr rfl (fun k _ => HeatBackwardDriftPairing.pairing F μ H S hS hcontr M hsem hsym _ _ _ _ v)
    _ = _ := hh

theorem noise_sum (u v : Process (E := E) F μ H) (n : ℕ) :
    (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),
      ∫ p,(Set.Ioc (HeatDualityGrid.point H n (k-1)) (HeatDualityGrid.point H n k)).indicator
        (fun s => inner ℝ (M (u (s,p.2))) (S (HeatDualityGrid.width n) (v (s,p.2)))) p.1 ∂energyMeasure μ H)=
      ∫ p,inner ℝ (M (u p)) (S (HeatDualityGrid.width n) (v p)) ∂energyMeasure μ H := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hv := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  exact HeatTimePartition.integral_selected μ H n (fun _ p => inner ℝ (M (u p)) (S (HeatDualityGrid.width n) (v p)))
    (fun _ _ => HeatL2Integrability.inner (energyMeasure μ H) _ _ (M.comp_memLp' hu)
      ((S (HeatDualityGrid.width n)).comp_memLp' hv))

end HeatPartitionPairings
#check @HeatPartitionPairings.control_sum
#print axioms HeatPartitionPairings.control_sum
#check @HeatPartitionPairings.drift_sum
#print axioms HeatPartitionPairings.drift_sum
#check @HeatPartitionPairings.noise_sum
#print HeatPartitionPairings.noise_sum
#print axioms HeatPartitionPairings.noise_sum
