import HeatZeroControlRecovery

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatVariationalMoments
open MeasureTheory Filter SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
  (hU : IsStronglyProgressive F (fun (_ : ℝ≥0) (_ : Ω) => (0:Base)))
  (hE : Integrable (fun _p : ℝ≥0 × Ω => ‖(0:Base)‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatVariationalForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) (fun _ _ => 0) hU hE g)
local notation "R" => SHE.RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem path_value (a : ℝ≥0) (ha : a≤H) : sol.weak.path a=ᵐ[μ]
    HeatMildSolution.value F μ H family family_continuous family_contraction M
      (HeatTerminalNaturality.integral F μ H basis J) g sol.weak.input a := by
  have hr := sol.weak.path_version a ha
  rw [HeatZeroControlRecovery.value_eq F μ H M (HeatTerminalNaturality.integral F μ H basis J) hU hE g sol.weak a] at hr
  exact hr

theorem conditional_mean (hlocal : SHE.StandardTerminalPastLocality J) {a c : ℝ≥0} (hac : a≤c) (hcH : c≤H) :
    μ[sol.weak.path c | F a]=ᵐ[μ] fun ω => family (c-a) (sol.weak.path a ω) := by
  have he := HeatMildRestart.conditional_mean F μ H family family_continuous family_contraction M family_semigroup basis J hlocal hac g sol.weak.input
  exact (condExp_congr_ae (path_value F μ H M basis J hU hE g sol c hcH)).trans
    (he.trans ((path_value F μ H M basis J hU hE g sol a (hac.trans hcH)).fun_comp (family (c-a))).symm)

theorem second_moment (hlocal : SHE.StandardTerminalPastLocality J) {a c : ℝ≥0} (hac : a≤c) (hcH : c≤H) :
    μ[(fun ω => (J.integral (SHE.StoppedItoInputs.stop F μ H c R) ω-
      J.integral (SHE.StoppedItoInputs.stop F μ H a R) ω) • sol.weak.path c ω) | F a]=ᵐ[μ]
      fun ω => ((c:ℝ)-(a:ℝ)) • ∫ v in (0:ℝ)..1,
        HeatIntervalCovariance.extend family ((1-v)*((c:ℝ)-(a:ℝ)))
          (M (HeatIntervalCovariance.extend family (v*((c:ℝ)-(a:ℝ))) (sol.weak.path a ω))) := by
  have hu := HeatZeroControlRecovery.fixed_point F μ H M (HeatTerminalNaturality.integral F μ H basis J) hU hE g sol.weak
  have he := HeatMildSecondMoment.second_moment F μ H family family_continuous family_contraction M family_semigroup basis J hlocal hac hcH g sol.weak.input hu
  have hleft : (fun ω => (J.integral (SHE.StoppedItoInputs.stop F μ H c R) ω-
      J.integral (SHE.StoppedItoInputs.stop F μ H a R) ω) • sol.weak.path c ω)=ᵐ[μ]
      fun ω => (J.integral (SHE.StoppedItoInputs.stop F μ H c R) ω-
      J.integral (SHE.StoppedItoInputs.stop F μ H a R) ω) •
        HeatMildSolution.value F μ H family family_continuous family_contraction M
          (HeatTerminalNaturality.integral F μ H basis J) g sol.weak.input c ω := by
    filter_upwards [path_value F μ H M basis J hU hE g sol c hcH] with ω hω
    rw [hω]
  apply (condExp_congr_ae hleft).trans (he.trans _)
  filter_upwards [path_value F μ H M basis J hU hE g sol a (hac.trans hcH)] with ω hω
  rw [←hω]

end HeatVariationalMoments
#check @HeatVariationalMoments.path_value
#print axioms HeatVariationalMoments.path_value
#check @HeatVariationalMoments.conditional_mean
#print axioms HeatVariationalMoments.conditional_mean
#check @HeatVariationalMoments.second_moment
#print HeatVariationalMoments.second_moment
#print axioms HeatVariationalMoments.second_moment
