import HeatShiftedNative
import HeatCanonicalPhysicalIto
import HeatVariationalMoments
import HeatCanonicalVariationalForward

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatCanonicalRestartMoments
open MeasureTheory Filter SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate

theorem exists_solution_and_moments (a H : ℝ≥0) (hH : 0<H) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1) (g : Base) :
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    let Fs := HeatShiftedBrownian.filtration F a
    let J := HeatShiftedNative.scalar F μ W HeatCanonicalUsual56.coordinate_filtered_brownian (fun ω => ω.continuous) a H
    let I := HeatTerminalNaturality.integral Fs μ H HeatCanonicalPhysicalIto.basis J
    ∃ hU : IsStronglyProgressive Fs (fun (_ : ℝ≥0) (_ : C(ℝ≥0,ℝ)) => (0:Base)),
      ∃ hE : Integrable (fun _p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖(0:Base)‖^2) (energyMeasure μ H),
      ∃ sol : HeatVariationalForwardModel.Solution Fs μ H (noise b hb hbound) I (fun _ _ => 0) hU hE g,
        sol.weak.path 0=ᵐ[μ] (fun _ => g) ∧
        ∀ r c : ℝ≥0,r ≤ c → c ≤ H →
          μ[sol.weak.path c | F (a+r)]=ᵐ[μ] (fun ω => family (c-r) (sol.weak.path r ω)) ∧
          μ[(fun ω => (W (a+c) ω-W (a+r) ω) • sol.weak.path c ω) | F (a+r)]=ᵐ[μ]
            (fun ω => ((c:ℝ)-(r:ℝ)) • ∫ v in (0:ℝ)..1,
              HeatIntervalCovariance.extend family ((1-v)*((c:ℝ)-(r:ℝ)))
                ((noise b hb hbound) (HeatIntervalCovariance.extend family (v*((c:ℝ)-(r:ℝ))) (sol.weak.path r ω)))) := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : IsSeparable μ := HeatCanonicalSeparable.completed_separable
  let basis := HeatCanonicalPhysicalIto.basis
  let Fs := HeatShiftedBrownian.filtration F a
  let J := HeatShiftedNative.scalar F μ W HeatCanonicalUsual56.coordinate_filtered_brownian (fun ω => ω.continuous) a H
  let I := HeatTerminalNaturality.integral Fs μ H basis J
  have hl := HeatShiftedNative.locality F μ W HeatCanonicalUsual56.coordinate_filtered_brownian (fun ω => ω.continuous) a H
  have hc := HeatShiftedNative.continuous_stopped F μ W HeatCanonicalUsual56.coordinate_filtered_brownian (fun ω => ω.continuous) a H
  have hn := HeatShiftedBrownian.contains_nulls HeatCanonicalNullComplete.contains_nulls a
  have hBDG := HeatShiftedNative.hilbert_bdg F μ W HeatCanonicalUsual56.coordinate_filtered_brownian
    (fun ω => ω.continuous) basis a H 3
  have hU : IsStronglyProgressive Fs (fun (_ : ℝ≥0) (_ : C(ℝ≥0,ℝ)) => (0:Base)) := isStronglyProgressive_const Fs 0
  have hE : Integrable (fun _p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖(0:Base)‖^2) (energyMeasure μ H) := by simp
  obtain ⟨sol⟩ := HeatVariationalForwardModel.exists_solution Fs μ H (noise b hb hbound) basis J hH hl hc hn
    (SHEStochastic.NativeScalarBDG.constant 3) hBDG (fun _ _ => 0) hU hE g
  refine ⟨hU,hE,sol,sol.weak.path_initial,?_⟩
  intro r c hrc hcH
  refine ⟨HeatVariationalMoments.conditional_mean Fs μ H (noise b hb hbound) basis J hU hE g sol hl hrc hcH,?_⟩
  have hs := HeatVariationalMoments.second_moment Fs μ H (noise b hb hbound) basis J hU hE g sol hl hrc hcH
  let R := SHE.RawCylindricalCoordinates.row Fs μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()
  have hrepr (t : ℝ≥0) (ht : t ≤ H) : (J.integral (SHE.StoppedItoInputs.stop Fs μ H t R) : C(ℝ≥0,ℝ) → ℝ)=ᵐ[μ]
      fun ω => W (a+t) ω-W a ω :=
    HeatShiftedNative.coordinate F μ W HeatCanonicalUsual56.coordinate_filtered_brownian (fun ω => ω.continuous) a H t ht
  have he : (fun ω => (W (a+c) ω-W (a+r) ω) • sol.weak.path c ω)=ᵐ[μ]
      fun ω => (J.integral (SHE.StoppedItoInputs.stop Fs μ H c R) ω-
        J.integral (SHE.StoppedItoInputs.stop Fs μ H r R) ω) • sol.weak.path c ω := by
    filter_upwards [hrepr c hcH,hrepr r (hrc.trans hcH)] with ω hc hr
    rw [hc,hr]
    congr 1
    ring
  exact (condExp_congr_ae he).trans hs

end HeatCanonicalRestartMoments
#check @HeatCanonicalRestartMoments.exists_solution_and_moments
#print axioms HeatCanonicalRestartMoments.exists_solution_and_moments
