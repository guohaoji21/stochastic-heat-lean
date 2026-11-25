import HeatBackwardCellRestriction
import HeatBackwardDriftKernel

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatBackwardInputCell
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatCovarianceOperator
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (g : E)
  (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
    MemLp (HeatBrownianProducts.products W t n) 2 μ)

include ht in
theorem input_cell (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    (j : {j // j ∈ Finset.Icc 1 N}) {a : ℝ≥0} (ha : t (j-1) ≤ a) :
    HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a (t j)
      (HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP) =
    HeatWeightedBackwardCell.input F μ H S (b := t j) ha (HeatBackwardNoise.coefficient W t j)
      (HeatBackwardNoise.coefficient_strong F μ W t N hP j)
      (HeatBackwardNoise.coefficient_memLp F μ W t N hP j)
      (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j) := by
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [HeatBackwardKernel.input_ae F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a (t j)
      (HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP),
    HeatBackwardNoise.process_ae S hS hcontr M F μ H W t N g hP,
    HeatWeightedCellInput.constant_ae F μ H a (t j) (HeatBackwardNoise.coefficient W t j)
      ((HeatBackwardNoise.coefficient_strong F μ W t N hP j).mono (F.mono ha))
      (HeatBackwardNoise.coefficient_memLp F μ W t N hP j)
      (S (t j-a) (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j))]
      with p hi hz hw
  rw [hi]
  dsimp only [HeatWeightedBackwardCell.input]
  rw [hw]
  by_cases hp : p.1 ∈ Ioc a (t j)
  · rw [Set.indicator_of_mem hp,hz,HeatBackwardCellRestriction.raw_cell S hS hcontr M W t ht N g
      j j.property p.1 ⟨ha.trans_lt hp.1,hp.2⟩ p.2]
    simp only [ContinuousLinearMap.id_apply,map_smul,PredictableSteps.step,if_pos hp]
    rw [HeatBackwardCell.kernel_constant S hsem hp.1.le hp.2]
  · simp [Set.indicator_of_notMem hp,PredictableSteps.step,hp]

include ht in
theorem drift_cell (j : {j // j ∈ Finset.Icc 1 N}) {a : ℝ≥0} (ha : t (j-1) ≤ a) :
    HeatBackwardDriftKernel.value F μ H S M a (t j)
      (HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP) =ᵐ[μ]
      (fun ω => ∫ s in Ioc a (t j), S (s-a) (M (HeatBackwardNoise.coefficient W t j ω • S (t j-s)
        (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j))) ∂timeMeasure H) := by
  have hz := (Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae
    (HeatBackwardNoise.process_ae S hS hcontr M F μ H W t N g hP)
  filter_upwards [Measure.ae_ae_of_ae_prod hz] with ω hω
  unfold HeatBackwardDriftKernel.value
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [hω] with s hs hmem
  dsimp only [Prod.swap] at hs
  rw [hs,HeatBackwardCellRestriction.raw_cell S hS hcontr M W t ht N g j j.property s
    ⟨ha.trans_lt hmem.1,hmem.2⟩ ω]

end HeatBackwardInputCell
#check @HeatBackwardInputCell.input_cell
#print axioms HeatBackwardInputCell.input_cell
#check @HeatBackwardInputCell.drift_cell
#print axioms HeatBackwardInputCell.drift_cell
