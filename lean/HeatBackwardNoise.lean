import HeatBackwardProcess
import HeatWeightedCellInput

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatBackwardNoise
open MeasureTheory SHE SHE.PredictableL2 HeatCovarianceOperator
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

def coefficient (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (j : ℕ) (ω : Ω) : ℝ :=
  HeatBrownianProducts.products W t (j-1) ω / ((t j:ℝ)-(t (j-1):ℝ))

def raw (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (g : E) (p : ℝ≥0 × Ω) : E :=
  ∑ j : {j // j ∈ Finset.Icc 1 N},
    PredictableSteps.step (t (j-1)) (t j) (coefficient W t j) p • S (t j-p.1)
      (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j)

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (g : E)
  (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
    MemLp (HeatBrownianProducts.products W t n) 2 μ)

include hP in
theorem coefficient_strong (j : {j // j ∈ Finset.Icc 1 N}) : StronglyMeasurable[F (t (j-1))] (coefficient W t j) := by
  have hh := (hP (j-1) ((Nat.sub_le _ _).trans (Finset.mem_Icc.mp j.property).2)).1
  change StronglyMeasurable[F (t (j-1))] (fun ω => HeatBrownianProducts.products W t (j-1) ω / ((t j:ℝ)-(t (j-1):ℝ)))
  simpa only [div_eq_mul_inv] using hh.mul_const (((t j:ℝ)-(t (j-1):ℝ))⁻¹)

include hP in
theorem coefficient_memLp (j : {j // j ∈ Finset.Icc 1 N}) : MemLp (coefficient W t j) 2 μ := by
  have hh := (hP (j-1) ((Nat.sub_le _ _).trans (Finset.mem_Icc.mp j.property).2)).2
  change MemLp (fun ω => HeatBrownianProducts.products W t (j-1) ω / ((t j:ℝ)-(t (j-1):ℝ))) 2 μ
  simpa only [div_eq_mul_inv] using hh.mul_const (((t j:ℝ)-(t (j-1):ℝ))⁻¹)

include hS hcontr hP in
theorem raw_predictable : StronglyMeasurable[F.predictable] (raw S hS hcontr M W t N g) := by
  let f (j : {j // j ∈ Finset.Icc 1 N}) (p : ℝ≥0 × Ω) : E :=
    PredictableSteps.step (t (j-1)) (t j) (coefficient W t j) p • S (t j-p.1)
      (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j)
  have he : raw S hS hcontr M W t N g = ∑ j, f j := by
    funext p
    simp only [raw,Finset.sum_apply,f]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro j _
  exact HeatWeightedCellInput.curve_measurable F (t (j-1)) (t j) (coefficient W t j)
    (coefficient_strong F μ W t N hP j)
    (fun s => S (t j-s) (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j))
    ((hS _).comp (HeatPredictableSemigroup.continuous_remaining (t j)))

include hS hcontr hP in
theorem raw_memLp : @MemLp _ _ F.predictable _ _ (raw S hS hcontr M W t N g) 2
    ((energyMeasure μ H).trim (predictable_le_product F)) := by
  apply memLp_finsetSum
  intro j _
  let q := HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j
  exact HeatWeightedCellInput.curve_memLp F μ H (t (j-1)) (t j) (coefficient W t j)
    (coefficient_strong F μ W t N hP j) (coefficient_memLp F μ W t N hP j)
    (fun s => S (t j-s) q) ((hS q).comp (HeatPredictableSemigroup.continuous_remaining (t j)))
    ‖q‖ (fun s => hcontr _ _)

def process : Process (E := E) F μ H :=
  (raw_memLp S hS hcontr M F μ H W t N g hP).toLp (raw S hS hcontr M W t N g)

theorem process_ae : process S hS hcontr M F μ H W t N g hP =ᵐ[energyMeasure μ H]
    raw S hS hcontr M W t N g :=
  ae_eq_of_ae_eq_trim (raw_memLp S hS hcontr M F μ H W t N g hP).coeFn_toLp

include hP in
theorem raw_energy_integrable : Integrable (fun p => ‖raw S hS hcontr M W t N g p‖^2) (energyMeasure μ H) :=
  (memLp_of_memLp_trim (predictable_le_product F) (raw_memLp S hS hcontr M F μ H W t N g hP)).norm.integrable_sq

end HeatBackwardNoise
#check @HeatBackwardNoise.coefficient_strong
#print axioms HeatBackwardNoise.coefficient_strong
#check @HeatBackwardNoise.coefficient_memLp
#print axioms HeatBackwardNoise.coefficient_memLp
#check @HeatBackwardNoise.raw_predictable
#print axioms HeatBackwardNoise.raw_predictable
#check @HeatBackwardNoise.raw_memLp
#print axioms HeatBackwardNoise.raw_memLp
#check @HeatBackwardNoise.process_ae
#print axioms HeatBackwardNoise.process_ae
#check @HeatBackwardNoise.raw_energy_integrable
#print axioms HeatBackwardNoise.raw_energy_integrable
