import SHEStochastic.ConditionalBracket

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatHilbertConditional
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {T : ℝ≥0}

theorem second_moment (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (u : Process (E := C) F μ T) :
    (∫ ω, ‖J.integral u ω‖ ^ 2 ∂μ) = ∫ ω, StochasticExponential.bracket F μ T u ω ∂μ := by
  have h : (∫ ω, ‖J.integral u ω‖ ^ 2 ∂μ) = ‖J.integral u‖ ^ 2 := by
    have hinner := real_inner_self_eq_norm_sq (J.integral u)
    rw [L2.inner_def] at hinner
    simpa only [real_inner_self_eq_norm_sq] using hinner
  rw [h, J.integral.norm_map, StochasticExponential.expected_bracket]

theorem setIntegral_second (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[F a] A) (u : Process (E := C) F μ T) :
    (∫ ω in A, ‖J.integral (post F μ T a u) ω‖ ^ 2 ∂μ) =
      ∫ ω in A, StochasticExponential.bracket F μ T (post F μ T a u) ω ∂μ := by
  have hL : (∫ ω, ‖J.integral (eventProcess F μ T a A hA u) ω‖ ^ 2 ∂μ) =
      ∫ ω in A, ‖J.integral (post F μ T a u) ω‖ ^ 2 ∂μ := by
    rw [← integral_indicator (F.le a A hA)]
    apply integral_congr_ae
    filter_upwards [hlocal a A hA u] with ω hω
    rw [hω]
    by_cases ha : ω ∈ A <;> simp [ha]
  have hR : (∫ ω, StochasticExponential.bracket F μ T (eventProcess F μ T a A hA u) ω ∂μ) =
      ∫ ω in A, StochasticExponential.bracket F μ T (post F μ T a u) ω ∂μ := by
    rw [← integral_indicator (F.le a A hA)]
    exact integral_congr_ae (SHEStochastic.ConditionalBracket.event_bracket a A hA u)
  rw [← hL, second_moment, hR]

theorem condExp_second (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0) (u : Process (E := C) F μ T) :
    μ[(fun ω ↦ ‖J.integral (post F μ T a u) ω‖ ^ 2) | F a] =ᵐ[μ]
      μ[StochasticExponential.bracket F μ T (post F μ T a u) | F a] := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le a)
    (Lp.memLp (J.integral (post F μ T a u))).norm.integrable_sq
    (fun s _ _ ↦ integrable_condExp.integrableOn) (fun s hs _ ↦ ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp (F.le a) (StochasticExponential.bracket_integrable F μ T _) hs]
  exact (setIntegral_second J hlocal a s hs u).symm

end HeatHilbertConditional

#check @HeatHilbertConditional.condExp_second
#print axioms HeatHilbertConditional.condExp_second
