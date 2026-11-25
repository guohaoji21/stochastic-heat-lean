import HeatUniformMoment
import HeatMomentUnweight

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatMomentSolution
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem exists_uniform (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B) (g : E) :
    ∃ u : Process (E := E) F μ H,
      u=HeatVolterraForcing.orbit F μ H S hS hcontr g+
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      ∃ R : ℝ, 0≤R ∧ ∀ᵐ t ∂timeMeasure H,
        HeatMomentBall.moment (μ:=μ) (fun ω => u (t,ω))≤ENNReal.ofReal R := by
  obtain ⟨γ,hγ,u,hu,hm⟩ := HeatUniformMoment.exists_weighted_solution F μ H S hS hcontr M hsem I B hB g
  have hh := HeatMomentUnweight.uniform F μ H γ hγ.le ((2:ℝ)^16*‖g‖^16)
    (PredictableExponential.scale F μ H (-γ) u) hm
  rw [PredictableExponential.cancel'] at hh
  exact ⟨u,hu,Real.exp (16*γ*(H:ℝ))*((2:ℝ)^16*‖g‖^16),by positivity,hh⟩

end HeatMomentSolution
#check @HeatMomentSolution.exists_uniform
#print axioms HeatMomentSolution.exists_uniform
