import HeatResolventH01Compact

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatH01Realization
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatDirichletResolventForm
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
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)

theorem embed_ae (v : Process (E := H01) F μ H) :
    HeatResolventH01Compact.embedProcess F μ H v=ᵐ[energyMeasure μ H] fun p => embed (v p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ae_eq_of_ae_eq_trim (embed.coeFn_compLpL v)

theorem exists_h01_path (hlocal : StandardTerminalPastLocality J) :
    ∃ v : Process (E := H01) F μ H,
      StronglyMeasurable[F.predictable] (v : ℝ≥0 × Ω → H01) ∧
      Integrable (fun p : ℝ≥0 × Ω => ‖v p‖^2) (energyMeasure μ H) ∧
      (fun p => embed (v p))=ᵐ[energyMeasure μ H] Function.uncurry sol.path := by
  obtain ⟨v,hv⟩ := HeatResolventH01Compact.exists_h01_input F μ H M basis J U hU hE g sol hlocal
  refine ⟨v,Lp.stronglyMeasurable v,?_,?_⟩
  · exact (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)).norm.integrable_sq
  · exact (embed_ae F μ H v).symm.trans (hv ▸ sol.input_path)

end HeatH01Realization
#check @HeatH01Realization.embed_ae
#print axioms HeatH01Realization.embed_ae
#check @HeatH01Realization.exists_h01_path
#print HeatH01Realization.exists_h01_path
#print axioms HeatH01Realization.exists_h01_path
