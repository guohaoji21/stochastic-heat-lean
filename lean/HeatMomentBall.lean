import HeatMildSolution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatMomentBall
open MeasureTheory Set Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0}
local notation "tm" => PredictableL2.timeMeasure

def moment (f : Ω → E) : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (‖f ω‖^16) ∂μ

theorem moment_congr {f g : Ω → E} (h : f=ᵐ[μ]g) : moment (μ:=μ) f=moment (μ:=μ) g :=
  lintegral_congr_ae (h.fun_comp (fun z => ENNReal.ofReal (‖z‖^16)))

def Ball (D : ℝ) : Set (Process (E := E) F μ H) :=
  {u | ∀ᵐ t ∂tm H,moment (μ:=μ) (fun ω => u (t,ω))≤ENNReal.ofReal D}

theorem zero_mem (D : ℝ) : (0 : Process (E := E) F μ H)∈Ball D := by
  change ∀ᵐ t ∂tm H,moment (μ:=μ) (fun ω => (0 : Process (E := E) F μ H) (t,ω))≤_
  have h := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim
    (Lp.coeFn_zero (α := ℝ≥0×Ω) (E := E) (p := 2)
      (μ := (energyMeasure μ H).trim (predictable_le_product F))))
  filter_upwards [h] with t ht
  rw [moment_congr ht]
  simp [moment]

/-- The essential timewise moment ball is closed in the predictable
L² norm. Extract a product-space subsequence, then use Fatou on each
time fibre. -/
theorem isClosed_ball (D : ℝ) : IsClosed (Ball (E := E) (F := F) (μ := μ) (H := H) D) := by
  apply isClosed_of_closure_subset
  intro u hu
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp hu
  let j := ambientIsometry (E := E) (energyMeasure μ H) (predictable_le_product F)
  have hJ : Tendsto (fun n => j (v n)) atTop (𝓝 (j u)) :=
    j.continuous.continuousAt.tendsto.comp hlim
  obtain ⟨φ,_,hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hJ).exists_seq_tendsto_ae
  have hφ' : ∀ᵐ p ∂energyMeasure μ H,Tendsto (fun n => v (φ n) p) atTop (𝓝 (u p)) := by
    filter_upwards [hφ,ambient_ae (energyMeasure μ H) (predictable_le_product F) u,
      ae_all_iff.mpr (fun n => ambient_ae (energyMeasure μ H) (predictable_le_product F) (v (φ n)))]
      with p hp hu hv
    change Tendsto (fun n => j (v (φ n)) p) atTop (𝓝 (j u p)) at hp
    rw [show j u p=u p from hu,show (fun n => j (v (φ n)) p)=(fun n => v (φ n) p) from funext hv] at hp
    exact hp
  have hVm (n : ℕ) : Measurable (v (φ n) : ℝ≥0×Ω → E) :=
    ((Lp.stronglyMeasurable (v (φ n))).mono (predictable_le_product F)).measurable
  have hh : ∀ᵐ t ∂tm H,∀ n,moment (μ:=μ) (fun ω => v (φ n) (t,ω))≤ENNReal.ofReal D :=
    ae_all_iff.mpr (fun n => hv (φ n))
  change ∀ᵐ t ∂tm H,moment (μ:=μ) (fun ω => u (t,ω))≤_
  filter_upwards [Measure.ae_ae_of_ae_prod hφ',hh] with t ht hb
  calc
    _ = ∫⁻ ω,liminf (fun n => ENNReal.ofReal (‖v (φ n) (t,ω)‖^16)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with ω hω
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hω.norm.pow 16)).liminf_eq.symm
    _ ≤ liminf (fun n => moment (μ:=μ) (fun ω => v (φ n) (t,ω))) atTop :=
      lintegral_liminf_le (fun n =>
        (((hVm n).comp (measurable_const.prodMk measurable_id)).norm.pow_const _).ennreal_ofReal)
    _ ≤ _ := liminf_le_of_frequently_le' (Filter.Eventually.of_forall hb).frequently


end HeatMomentBall
#check @HeatMomentBall.moment_congr
#print axioms HeatMomentBall.moment_congr
#check @HeatMomentBall.zero_mem
#print axioms HeatMomentBall.zero_mem
#check @HeatMomentBall.isClosed_ball
#print axioms HeatMomentBall.isClosed_ball
