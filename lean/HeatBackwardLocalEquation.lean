import HeatBackwardClosedCell
import HeatBackwardInputCell
import HeatBackwardStochasticKernel
import HeatBackwardGluing

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatBackwardLocalEquation
open MeasureTheory Set SHE SHE.PredictableL2 SHE.HilbertColumns HeatCovarianceOperator
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

include hS hcontr in
theorem local_equation (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s ≤ H → J.integral (StoppedItoInputs.stop F μ H s R) =ᵐ[μ] W s)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hN : 1 ≤ N)
    (hstep : ∀ n, n < N → t n < t (n+1)) (hT : t N ≤ H) (g : E)
    (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ)
    (j : {j // j ∈ Finset.Icc 1 N}) (a : ℝ≥0) (ha : a ∈ Icc (t (j-1)) (t j)) :
    HeatBackwardGluing.Equation μ S
      (fun a b => HeatBackwardDriftKernel.value F μ H S M a b
        (HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP))
      (fun a b => HeatBackwardStochasticKernel.value F μ H S hS hcontr basis J a b
        (HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP))
      (HeatBackwardProcess.state S hS hcontr M H W t N g) a (t j) := by
  let q := HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j
  let C := HeatBackwardNoise.coefficient W t j
  have hC := HeatBackwardNoise.coefficient_strong F μ W t N hP j
  have hCm := HeatBackwardNoise.coefficient_memLp F μ W t N hP j
  have he := HeatWeightedBackwardCell.mild_equation F μ H S M basis J hlocal W hW ha.1 ha.2
    ((ht (Finset.mem_Icc.mp j.property).2).trans hT) C hC hCm q
  rw [←HeatBackwardInputCell.input_cell S hS hcontr M F μ H W t ht N g hP hsem j ha.1] at he
  have hd := HeatBackwardInputCell.drift_cell S hS hcontr M F μ H W t ht N g hP j ha.1
  have hz (ω : Ω) : HeatBackwardProcess.state S hS hcontr M H W t N g (t j) ω =
      C ω • ((W (t j) ω-W (t (j-1)) ω) • q) := by
    rw [HeatBackwardClosedCell.cell_value S hS hcontr M hzero W t ht N hN hstep hT g j j.property
      (t j) ⟨ht (Nat.sub_le _ _),le_rfl⟩ ω]
    change C ω • HeatBackwardCell.state H S M W (t (j-1)) (t j) q (t j) ω = _
    rw [HeatBackwardCell.terminal H S M hzero]
  filter_upwards [he,hd] with ω he hd
  change HeatBackwardProcess.state S hS hcontr M H W t N g a ω = _
  rw [HeatBackwardClosedCell.cell_value S hS hcontr M hzero W t ht N hN hstep hT g j j.property a ha ω]
  change C ω • HeatBackwardCell.state H S M W (t (j-1)) (t j) q a ω = _
  rw [he,hz,hd]
  rfl

end HeatBackwardLocalEquation
#check @HeatBackwardLocalEquation.local_equation
#print axioms HeatBackwardLocalEquation.local_equation
