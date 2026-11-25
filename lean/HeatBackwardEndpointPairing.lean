import HeatBackwardProcess
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatBackwardEndpointPairing
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)

theorem terminal (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (hN : 1≤N)
    (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=H) (g : E) (Y Z : Lp E 2 μ)
    (hZ : Z=ᵐ[μ] HeatBackwardProcess.state S hS hcontr M H W t N g H) :
    inner ℝ Y Z=(∫ ω,HeatBrownianProducts.products W t N ω*inner ℝ g (Y ω) ∂μ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hZ] with ω hz
  have ht := HeatBackwardProcess.terminal S hS hcontr M (H := H) hzero W t N hN hstep g ω
  rw [hTN] at ht
  rw [hz,ht,inner_smul_right]
  exact congrArg (fun r => HeatBrownianProducts.products W t N ω*r) (real_inner_comm _ _)

theorem initial (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0)
    (N : ℕ) (hN : 1≤N) (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=H) (g₀ g : E)
    (V Z : ℝ≥0 → Lp E 2 μ) (hV : V 0=Lp.const 2 μ g₀)
    (hZ : Z 0=ᵐ[μ] HeatBackwardProcess.state S hS hcontr M H W t N g 0) :
    inner ℝ (V 0) (Z 0)=inner ℝ
      (HeatBackwardChain.stateAt (HeatCovarianceOperator.covariance S hS hcontr M) (fun k => t k-t (k-1)) N g 0) g₀ := by
  rw [hV,L2.inner_def]
  have hpoint (ω : Ω) := HeatBackwardProcess.initial S hS hcontr M (H := H) W t ht N hN (hstep 0 (by omega)) hTN.le g ω
  rw [ht0] at hpoint
  have he : (fun ω => inner ℝ (Lp.const 2 μ g₀ ω) (Z 0 ω))=ᵐ[μ]
      (fun _ => inner ℝ g₀ (HeatBackwardChain.stateAt (HeatCovarianceOperator.covariance S hS hcontr M)
        (fun k => t k-t (k-1)) N g 0)) := by
    filter_upwards [Lp.coeFn_const 2 μ g₀,hZ] with ω hc hz
    rw [hc,hz,hpoint ω]
    rfl
  rw [integral_congr_ae he,integral_const]
  have hm : μ.real Set.univ=1 := by simp [Measure.real]
  rw [hm,one_smul]
  exact (real_inner_comm g₀
    (HeatBackwardChain.stateAt (HeatCovarianceOperator.covariance S hS hcontr M) (fun k => t k-t (k-1)) N g 0)).symm

end HeatBackwardEndpointPairing
#check @HeatBackwardEndpointPairing.terminal
#print axioms HeatBackwardEndpointPairing.terminal
#check @HeatBackwardEndpointPairing.initial
#print HeatBackwardEndpointPairing.initial
#print axioms HeatBackwardEndpointPairing.initial
