import SHE.StandardTerminalPastLocality
import SHE.StandardTerminalNovikov
import SHE.PastItoAlgebra
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace HeatHilbertFutureCenter
open MeasureTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℝ≥0}

theorem condExp_post_zero (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0) (u : Process (E := C) F μ T) :
    μ[(J.integral (post F μ T a u) : Ω → E) | F a] =ᵐ[μ] (fun _ => (0 : E)) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le a)
    ((Lp.memLp (J.integral (post F μ T a u))).integrable one_le_two)
    (fun _ _ _ => (integrable_const (0 : E)).integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_zero.aestronglyMeasurable).symm
  change (∫ _ω in A, (0 : E) ∂μ) = _
  rw [integral_zero, ← integral_indicator (F.le a A hA)]
  exact ((integral_congr_ae (hlocal a A hA u).symm).trans (J.centered _)).symm

variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]

theorem condExp_increment_zero (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0} (hab : a ≤ b)
    (u : Process (E := C) F μ T) :
    μ[(fun ω => J.integral (stop F μ T b u) ω - J.integral (stop F μ T a u) ω) | F a]
      =ᵐ[μ] (fun _ => (0 : E)) := by
  have hi : (J.integral (post F μ T a (stop F μ T b u)) : Ω → E) =ᵐ[μ]
      fun ω => J.integral (stop F μ T b u) ω - J.integral (stop F μ T a u) ω := by
    rw [PastItoAlgebra.post_stop_eq_sub F μ T a b hab, map_sub]
    exact Lp.coeFn_sub _ _
  exact (condExp_congr_ae hi.symm).trans (condExp_post_zero J hlocal a _)


/-- The deterministic/past term in a mild decomposition is the conditional
mean when the remaining term is a future integral increment. -/
theorem conditional_mean_of_mild_decomposition
    (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0} (hab : a ≤ b)
    (u : Process (E := C) F μ T) (V Z : Ω → E)
    (hV : Integrable V μ) (hVmeas : AEStronglyMeasurable[F a] V μ)
    (hZ : Z =ᵐ[μ] fun ω => V ω + (J.integral (stop F μ T b u) ω -
      J.integral (stop F μ T a u) ω)) :
    μ[Z | F a] =ᵐ[μ] V := by
  have hn : Integrable (fun ω => J.integral (stop F μ T b u) ω -
      J.integral (stop F μ T a u) ω) μ :=
    ((Lp.memLp (J.integral (stop F μ T b u))).integrable one_le_two).sub
      ((Lp.memLp (J.integral (stop F μ T a u))).integrable one_le_two)
  have he := condExp_congr_ae (m := F a) hZ
  have hs := condExp_add hV hn (F a)
  have hv := condExp_of_aestronglyMeasurable' (F.le a) hVmeas hV
  have hz := condExp_increment_zero J hlocal hab u
  filter_upwards [he,hs,hv,hz] with ω he hs hv hz
  change μ[Z | F a] ω = μ[V + (fun ω => J.integral (stop F μ T b u) ω -
    J.integral (stop F μ T a u) ω) | F a] ω at he
  simp only [Pi.add_apply] at hs
  rw [hs,hv,hz,add_zero] at he
  exact he


/-- First conditional moment for an already established mild heat identity. -/
theorem conditional_mean_of_heat_mild
    (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0} (hab : a ≤ b)
    (u : Process (E := C) F μ T) (S : E →L[ℝ] E) (Y₀ Z : Ω → E)
    (hY₀ : MemLp Y₀ 2 μ) (hY₀meas : StronglyMeasurable[F a] Y₀)
    (hZ : Z =ᵐ[μ] fun ω => S (Y₀ ω) + (J.integral (stop F μ T b u) ω -
      J.integral (stop F μ T a u) ω)) :
    μ[Z | F a] =ᵐ[μ] fun ω => S (Y₀ ω) := by
  apply conditional_mean_of_mild_decomposition J hlocal hab u (fun ω => S (Y₀ ω)) Z
  · exact (S.comp_memLp' hY₀).integrable one_le_two
  · exact (S.continuous.comp_stronglyMeasurable hY₀meas).aestronglyMeasurable
  · exact hZ

end HeatHilbertFutureCenter
#check @HeatHilbertFutureCenter.condExp_post_zero
#print axioms HeatHilbertFutureCenter.condExp_post_zero
#check @HeatHilbertFutureCenter.condExp_increment_zero
#print axioms HeatHilbertFutureCenter.condExp_increment_zero

#check @HeatHilbertFutureCenter.conditional_mean_of_mild_decomposition
#print axioms HeatHilbertFutureCenter.conditional_mean_of_mild_decomposition

#check @HeatHilbertFutureCenter.conditional_mean_of_heat_mild
#print axioms HeatHilbertFutureCenter.conditional_mean_of_heat_mild
