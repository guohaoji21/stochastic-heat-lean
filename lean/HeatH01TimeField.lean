import HeatH01Realization

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatH01TimeField
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatDirichletResolventForm
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : MeasurableSpace H01 := borel H01
local instance : BorelSpace H01 := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : SecondCountableTopology H01 := by unfold H01;infer_instance
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (H : ℝ≥0) (v : Process (E := H01) F μ H)

theorem measurable : Measurable (v : ℝ≥0 × Ω → H01) :=
  ((Lp.stronglyMeasurable v).mono (predictable_le_product F)).measurable

theorem memLp : MemLp (v : ℝ≥0 × Ω → H01) 2 (energyMeasure μ H) :=
  memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)

def value : ℝ≥0 → Lp H01 2 μ := HeatTimeLpField.value μ (v : ℝ≥0 × Ω → H01)

theorem slices : ∀ᵐ t ∂timeMeasure H, value F μ H v t=ᵐ[μ] fun ω => v (t,ω) :=
  HeatTimeLpField.value_ae μ _ (measurable F μ H v) H (memLp F μ H v)

theorem integrable {T : ℝ≥0} (hT : T≤H) : Integrable (value F μ H v) (timeMeasure T) := by
  have hm := HeatTimeLpField.square_integrable μ (v : ℝ≥0 × Ω → H01) (measurable F μ H v) H (memLp F μ H v)
  exact (hm.mono_measure (HeatTimeRestriction.mono hT)).integrable (by norm_num)

theorem embed_slices (u : Process (E := Base) F μ H) (V : ℝ≥0 → Lp Base 2 μ)
    (hv : HeatResolventH01Compact.embedProcess F μ H v=u)
    (hV : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t) :
    ∀ᵐ t ∂timeMeasure H, (embed.compLpL 2 μ) (value F μ H v t)=V t := by
  have hraw : (fun p => embed (v p))=ᵐ[energyMeasure μ H] u := by
    rw [←hv]
    exact (HeatH01Realization.embed_ae F μ H v).symm
  have hc := Measure.ae_ae_of_ae_prod hraw
  filter_upwards [hc,hV,slices F μ H v] with t he hu hs
  apply Lp.ext
  filter_upwards [embed.coeFn_compLpL (value F μ H v t),hs,he,hu] with ω hm hw hx hy
  rw [hm,hw,hx,hy]

end HeatH01TimeField
#check @HeatH01TimeField.measurable
#print axioms HeatH01TimeField.measurable
#check @HeatH01TimeField.memLp
#print axioms HeatH01TimeField.memLp
#check @HeatH01TimeField.slices
#print axioms HeatH01TimeField.slices
#check @HeatH01TimeField.integrable
#print axioms HeatH01TimeField.integrable
#check @HeatH01TimeField.embed_slices
#print HeatH01TimeField.embed_slices
#print axioms HeatH01TimeField.embed_slices
