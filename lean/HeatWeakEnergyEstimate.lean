import HeatWeakEnergyDifference
import HeatStoppedProcessBound
import HeatStoppedSliceEnergy
import HeatResolventGradient
import HeatResolventLpConvergence
import HeatZeroGronwall
import HeatWeakEnergyIto
import HeatItoNormEnergyAt
import SHE.StoppedDampingClock

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatWeakEnergyEstimate
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatDirichletResolvent HeatWeakEnergyEquation
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
variable (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (s₁ s₂ : HeatWeakEnergyModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)


theorem input_slices : ∀ᵐ t ∂timeMeasure H,
    (fun ω => (s₁.input-s₂.input) (t,ω))=ᵐ[μ]
      HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ t := by
  have hraw := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub s₁.input s₂.input))
  filter_upwards [s₁.input_slices,s₂.input_slices,hraw] with t h1 h2 hraw
  filter_upwards [h1,h2,hraw,Lp.coeFn_sub (s₁.value t) (s₂.value t)] with ω h1 h2 hr hv
  change (s₁.input-s₂.input) (t,ω)=(s₁.value t-s₂.value t) ω
  rw [hr,hv]
  simp only [Pi.sub_apply,h1,h2]

theorem noise_bound {a : ℝ} (ha : 1 ≤ a) :
    ∀ᵐ p ∂energyMeasure μ H,
      ‖HeatWeakEnergyDifference.noise F μ H M basis J U hU hE g s₁ s₂ a ha p‖ ≤
        ‖M‖*‖(s₁.input-s₂.input) p‖ := by
  let R := smoothing a ha
  let n₁ := HeatWeakEnergyProcess.noise F μ H M basis J U hU hE g s₁ a ha
  let n₂ := HeatWeakEnergyProcess.noise F μ H M basis J U hU hE g s₂ a ha
  have hn₁ : n₁=ᵐ[energyMeasure μ H] fun p => R (M (s₁.input p)) :=
    (HeatPredictableLinearMap.map_ae F μ H R (HeatWeakStochasticInput.noise F μ H M s₁.input)).trans
      ((HeatWeakStochasticInput.noise_ae F μ H M s₁.input).fun_comp (fun x => R x))
  have hn₂ : n₂=ᵐ[energyMeasure μ H] fun p => R (M (s₂.input p)) :=
    (HeatPredictableLinearMap.map_ae F μ H R (HeatWeakStochasticInput.noise F μ H M s₂.input)).trans
      ((HeatWeakStochasticInput.noise_ae F μ H M s₂.input).fun_comp (fun x => R x))
  filter_upwards [hn₁,hn₂,ae_eq_of_ae_eq_trim (Lp.coeFn_sub n₁ n₂),
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub s₁.input s₂.input)] with p h1 h2 hn hi
  change ‖(n₁-n₂) p‖ ≤ ‖M‖*‖(s₁.input-s₂.input) p‖
  rw [hn,hi]
  simp only [Pi.sub_apply,h1,h2]
  have he : R (M (s₁.input p))-R (M (s₂.input p))=R (M (s₁.input p-s₂.input p)) := by rw [map_sub,map_sub]
  rw [he]
  exact (smoothing_contraction ha _).trans (M.le_opNorm _)

theorem regularized_bound (hlocal : StandardTerminalPastLocality J) {a : ℝ} (ha : 1 ≤ a)
    {T : ℝ≥0} (hT : T ≤ H) :
    ‖((smoothing a ha).compLpL 2 μ) (HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ T)‖^2 ≤
      ‖M‖^2*(∫ t,‖HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ t‖^2 ∂timeMeasure T) := by
  have he := HeatWeakEnergyDifference.energy F μ H M basis J U hU hE g s₁ s₂ hlocal ha hT
  have hpoint (t : ℝ≥0) : inner ℝ
      (HeatWeakEnergyDifference.drift F μ H M basis J U hU hE g s₁ s₂ a ha t)
      (((smoothing a ha).compLpL 2 μ) (HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ t)) ≤ 0 := by
    have hh := HeatResolventGradient.lp_drift_energy μ ha
      (HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ t)
    change inner ℝ
      (HeatWeakEnergyDifference.drift F μ H M basis J U hU hE g s₁ s₂ a ha t)
      (((smoothing a ha).compLpL 2 μ) (HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ t))=_ at hh
    rw [hh]
    exact neg_nonpos.mpr (sq_nonneg _)
  have hnonpos := integral_nonpos (μ := timeMeasure T) hpoint
  have hle : ‖((smoothing a ha).compLpL 2 μ)
      (HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ T)‖^2 ≤
      ‖StoppedItoInputs.stop F μ H T (HeatWeakEnergyDifference.noise F μ H M basis J U hU hE g s₁ s₂ a ha)‖^2 := by linarith
  have hb := HeatStoppedProcessBound.square F μ H
    (HeatWeakEnergyDifference.noise F μ H M basis J U hU hE g s₁ s₂ a ha) (s₁.input-s₂.input) ‖M‖ (norm_nonneg _)
    (noise_bound F μ H M basis J U hU hE g s₁ s₂ ha) T
  rw [HeatStoppedSliceEnergy.energy F μ H (s₁.input-s₂.input)
    (HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂)
    (input_slices F μ H M basis J U hU hE g s₁ s₂) hT] at hb
  exact hle.trans hb

theorem norm_bound (hlocal : StandardTerminalPastLocality J) {T : ℝ≥0} (hT : T ≤ H) :
    ‖HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ T‖^2 ≤
      ‖M‖^2*(∫ t,‖HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ t‖^2 ∂timeMeasure T) := by
  have hl := (HeatResolventLpConvergence.tendsto μ
    (HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ T)).norm.pow 2
  apply le_of_tendsto hl
  exact Eventually.of_forall fun n => regularized_bound F μ H M basis J U hU hE g s₁ s₂ hlocal
    (a := (n:ℝ)+1) (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n;linarith) hT

theorem value_same (hlocal : StandardTerminalPastLocality J) (T : ℝ≥0) (hT : T ≤ H) : s₁.value T=s₂.value T := by
  have hz := HeatZeroGronwall.zero H
    (fun t => ‖HeatWeakEnergyDifference.value F μ H M basis J U hU hE g s₁ s₂ t‖^2)
    ((s₁.mean_square_continuous.sub s₂.mean_square_continuous).norm.pow 2)
    (fun t => sq_nonneg _) (‖M‖^2) (sq_nonneg _)
    (fun t ht => norm_bound F μ H M basis J U hU hE g s₁ s₂ hlocal ht) T hT
  apply sub_eq_zero.mp
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end HeatWeakEnergyEstimate
#check @HeatWeakEnergyEstimate.input_slices
#print axioms HeatWeakEnergyEstimate.input_slices
#check @HeatWeakEnergyEstimate.noise_bound
#print axioms HeatWeakEnergyEstimate.noise_bound
#check @HeatWeakEnergyEstimate.regularized_bound
#print axioms HeatWeakEnergyEstimate.regularized_bound
#check @HeatWeakEnergyEstimate.norm_bound
#print axioms HeatWeakEnergyEstimate.norm_bound
#check @HeatWeakEnergyEstimate.value_same
#print axioms HeatWeakEnergyEstimate.value_same
