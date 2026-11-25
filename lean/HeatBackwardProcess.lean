import HeatBackwardNodes
import HeatContinuousCells
import HeatBrownianProducts

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatBackwardProcess
open MeasureTheory SHE SHE.PredictableL2 HeatCovarianceOperator
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

def state (H : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (g : E) (s : ℝ≥0) (ω : Ω) : E :=
  HeatContinuousCells.paste t (fun j s => HeatBackwardNodes.cellState S hS hcontr M H W t N g j s ω) (N-1) s

include hS hcontr in
theorem continuous_paths {H : ℝ≥0} (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (W : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun s => W s ω))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hN : 1 ≤ N)
    (hstep : ∀ n, n < N → t n < t (n+1)) (hT : t N ≤ H) (g : E) (ω : Ω) :
    Continuous (fun s => state S hS hcontr M H W t N g s ω) := by
  apply HeatContinuousCells.continuous_prefix t
    (fun j s => HeatBackwardNodes.cellState S hS hcontr M H W t N g j s ω) N hstep
  · intro j hj hjN
    exact HeatWeightedBackwardCell.state_continuous H S hS hcontr M W hc
      ((ht hjN).trans hT)
      (fun ω => HeatBrownianProducts.products W t (j-1) ω/((t j:ℝ)-(t (j-1):ℝ)))
      (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j) ω
  · intro j hj hjN
    exact HeatBackwardNodes.node_match S hS hcontr M hzero W t N g hj hjN
      (hstep j hjN) ((ht (Nat.succ_le_iff.mpr hjN)).trans hT) ω
  · omega

include hS hcontr in
theorem terminal {H : ℝ≥0} (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (hN : 1 ≤ N)
    (hstep : ∀ n, n < N → t n < t (n+1)) (g : E) (ω : Ω) :
    state S hS hcontr M H W t N g (t N) ω = HeatBrownianProducts.products W t N ω • g := by
  have hidx : N-1+1=N := by omega
  have ht : t (N-1) < t N := by simpa only [hidx] using hstep (N-1) (by omega)
  unfold state
  rw [HeatContinuousCells.tail_value _ _ (N-1) (t N) ht,hidx]
  unfold HeatBackwardNodes.cellState
  rw [HeatBackwardNodes.right_value S M hzero,HeatBackwardChain.terminal]
  have he : HeatBrownianProducts.products W t N ω =
      HeatBrownianProducts.products W t (N-1) ω * (W (t N) ω-W (t (N-1)) ω) /
        ((t N:ℝ)-(t (N-1):ℝ)) := by
    conv_lhs => rw [←hidx]
    rw [HeatBrownianProducts.products]
    simp only [hidx]
  rw [he]

include hS hcontr in
theorem initial {H : ℝ≥0} (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (N : ℕ) (hN : 1 ≤ N) (hstep : t 0 < t 1) (hT : t N ≤ H) (g : E) (ω : Ω) :
    state S hS hcontr M H W t N g (t 0) ω =
      HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g 0 := by
  unfold state
  rw [HeatContinuousCells.initial_value _ ht]
  unfold HeatBackwardNodes.cellState
  simp only [Nat.sub_self]
  rw [HeatBackwardNodes.left_value S hS hcontr M hstep ((ht hN).trans hT)]
  simp only [HeatBrownianProducts.products,one_smul]
  exact (HeatBackwardChain.recurrence (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g
    (j := 1) (by omega) hN).symm

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

include hS hcontr in
theorem cell_adapted {H : ℝ≥0} (W : ℝ≥0 → Ω → ℝ)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s))
    (t : ℕ → ℝ≥0) (N : ℕ) (g : E)
    (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n))
    {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) (s : ℝ≥0) (hleft : t (j-1) ≤ s) :
    StronglyMeasurable[F s] (fun ω => HeatBackwardNodes.cellState S hS hcontr M H W t N g j s ω) := by
  let q := HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j
  have hPa := (hP (j-1) ((Nat.sub_le _ _).trans hjN)).mono (F.mono hleft)
  have hC : StronglyMeasurable[F s] (fun ω => HeatBrownianProducts.products W t (j-1) ω /
      ((t j:ℝ)-(t (j-1):ℝ))) := by
    simpa only [div_eq_mul_inv] using hPa.mul_const (((t j:ℝ)-(t (j-1):ℝ))⁻¹)
  have hd := (hWa s).sub ((hWa (t (j-1))).mono (F.mono hleft))
  have hZ : StronglyMeasurable[F s] (fun ω => HeatBackwardCell.state H S M W (t (j-1)) (t j) q s ω) :=
    (hd.smul_const (S (t j-s) q)).add stronglyMeasurable_const
  exact hC.smul hZ

include hS hcontr in
theorem adapted {H : ℝ≥0} (W : ℝ≥0 → Ω → ℝ)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s))
    (t : ℕ → ℝ≥0) (ht0 : t 0=0) (N : ℕ) (hN : 1 ≤ N) (g : E)
    (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n))
    (s : ℝ≥0) : StronglyMeasurable[F s] (fun ω => state S hS hcontr M H W t N g s ω) := by
  have hs0 : t 0 ≤ s := by rw [ht0]; exact zero_le
  have hpre : ∀ n, n < N → StronglyMeasurable[F s] (fun ω =>
      HeatContinuousCells.paste t (fun j r => HeatBackwardNodes.cellState S hS hcontr M H W t N g j r ω) n s) := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact cell_adapted S hS hcontr M F W hWa t N g hP (j:=1) (by omega) hN s hs0
    | succ n ih =>
      intro hn
      by_cases hs : s ≤ t (n+1)
      · simpa only [HeatContinuousCells.paste,hs,ite_true] using ih (by omega)
      · have hh : t (n+1) ≤ s := (lt_of_not_ge hs).le
        simpa only [HeatContinuousCells.paste,hs,ite_false] using
          cell_adapted S hS hcontr M F W hWa t N g hP (j:=n+2) (by omega) (by omega) s hh
  exact hpre (N-1) (by omega)


include hS hcontr in
theorem predictable {H : ℝ≥0} (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (W : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun s => W s ω))
    (hWa : ∀ s, StronglyMeasurable[F s] (W s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1 ≤ N)
    (hstep : ∀ n, n < N → t n < t (n+1)) (hT : t N ≤ H) (g : E)
    (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n)) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => state S hS hcontr M H W t N g p.1 p.2) := by
  change IsStronglyPredictable F (fun s ω => state S hS hcontr M H W t N g s ω)
  apply StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · exact adapted S hS hcontr M F W hWa t ht0 N hN g hP
  · intro ω s
    exact (continuous_paths S hS hcontr M hzero W hc t ht N hN hstep hT g ω).continuousWithinAt

end HeatBackwardProcess
#check @HeatBackwardProcess.continuous_paths
#print axioms HeatBackwardProcess.continuous_paths
#check @HeatBackwardProcess.terminal
#print axioms HeatBackwardProcess.terminal
#check @HeatBackwardProcess.initial
#print axioms HeatBackwardProcess.initial
#check @HeatBackwardProcess.cell_adapted
#print axioms HeatBackwardProcess.cell_adapted
#check @HeatBackwardProcess.adapted
#print axioms HeatBackwardProcess.adapted

#check @HeatBackwardProcess.predictable
#print axioms HeatBackwardProcess.predictable
