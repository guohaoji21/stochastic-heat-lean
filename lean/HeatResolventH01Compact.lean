import HeatUniformGradientEnergy
import HeatResolventLpConvergence
import EllipticPdes.Analysis.DirectMethodForm

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatResolventH01Compact
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatDirichletResolventForm HeatDirichletResolvent
open scoped NNReal ENNReal Topology
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

def embedProcess : Process (E := H01) F μ H →L[ℝ] Process (E := Base) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact embed.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))

def liftInput (a : ℝ) (ha : 1≤a) (u : Process (E := Base) F μ H) : Process (E := H01) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ((HeatResolventGradient.lift a ha).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u

theorem embed_liftInput {a : ℝ} (ha : 1≤a) (u : Process (E := Base) F μ H) :
    embedProcess F μ H (liftInput F μ H a ha u)=HeatPredictableLinearMap.map F μ H (smoothing a ha) u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  filter_upwards [embed.coeFn_compLpL (liftInput F μ H a ha u),
    (HeatResolventGradient.lift a ha).coeFn_compLpL u,(smoothing a ha).coeFn_compLpL u] with p he hl hs
  change embedProcess F μ H (liftInput F μ H a ha u) p=embed (liftInput F μ H a ha u p) at he
  change liftInput F μ H a ha u p=HeatResolventGradient.lift a ha (u p) at hl
  change HeatPredictableLinearMap.map F μ H (smoothing a ha) u p=smoothing a ha (u p) at hs
  rw [he,hl,hs,HeatResolventGradient.embed_lift]

theorem tendsto_embedded (u : Process (E := Base) F μ H) :
    Tendsto (fun n : ℕ => embedProcess F μ H (liftInput F μ H ((n:ℝ)+1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n;linarith) u)) atTop (𝓝 u) := by
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure;infer_instance
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have ht := HeatResolventLpConvergence.tendsto ((energyMeasure μ H).trim (predictable_le_product F)) u
  simpa only [embed_liftInput,HeatPredictableLinearMap.map,HeatResolventApproximation.approx] using ht

variable (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

theorem liftInput_bound (hlocal : StandardTerminalPastLocality J) {a : ℝ} (ha : 1≤a) :
    ‖liftInput F μ H a ha sol.input‖^2≤‖sol.input‖^2+
      HeatUniformGradientEnergy.constant F μ H M basis J U hU hE g sol/2 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hd := HeatResolventGradient.lp_norm_decomposition
    ((energyMeasure μ H).trim (predictable_le_product F)) ha sol.input
  change ‖liftInput F μ H a ha sol.input‖^2=
    ‖HeatPredictableLinearMap.map F μ H (smoothing a ha) sol.input‖^2+
    ‖HeatPredictableLinearMap.map F μ H (HeatResolventGradient.gradient a ha) sol.input‖^2 at hd
  have hn := HeatPredictableLinearMap.contraction F μ H (smoothing a ha) (smoothing_contraction ha) sol.input
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hg := HeatUniformGradientEnergy.bound F μ H M basis J U hU hE g sol hlocal ha
  linarith

theorem exists_h01_input (hlocal : StandardTerminalPastLocality J) :
    ∃ v : Process (E := H01) F μ H, embedProcess F μ H v=sol.input := by
  let B := ‖sol.input‖^2+HeatUniformGradientEnergy.constant F μ H M basis J U hU hE g sol/2
  have hB : 0≤B := by
    have hk := HeatUniformGradientEnergy.constant_nonnegative F μ H M basis J U hU hE g sol
    dsimp [B];positivity
  let w : ℕ → Process (E := H01) F μ H := fun n =>
    liftInput F μ H ((n:ℝ)+1) (by have hn := Nat.cast_nonneg (α := ℝ) n;linarith) sol.input
  have hb (n : ℕ) : ‖w n‖≤Real.sqrt B := by
    have hn := liftInput_bound F μ H M basis J U hU hE g sol hlocal
      (a := (n:ℝ)+1) (by have hn := Nat.cast_nonneg (α := ℝ) n;linarith)
    change ‖w n‖^2≤B at hn
    nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg B,norm_nonneg (w n)]
  obtain ⟨v,σ,hσ,hweak⟩ := EllipticPdes.Analysis.exists_weakLimit hb
  refine ⟨v,?_⟩
  apply Eq.symm
  apply EllipticPdes.Analysis.eq_of_tendsto_of_weakLimit hweak
  exact (tendsto_embedded F μ H sol.input).comp hσ.tendsto_atTop

end HeatResolventH01Compact
#check @HeatResolventH01Compact.embed_liftInput
#print axioms HeatResolventH01Compact.embed_liftInput
#check @HeatResolventH01Compact.tendsto_embedded
#print axioms HeatResolventH01Compact.tendsto_embedded
#check @HeatResolventH01Compact.liftInput_bound
#print axioms HeatResolventH01Compact.liftInput_bound
#check @HeatResolventH01Compact.exists_h01_input
#print HeatResolventH01Compact.exists_h01_input
#print axioms HeatResolventH01Compact.exists_h01_input
