import HeatTimeRestriction
import SHEStochastic.MeasurableHilbertL2Realization
import SHE.ProcessEnergy
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatTimeLpField
open MeasureTheory Filter Set SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (f : ℝ≥0 × Ω → E) (hf : Measurable f)
local instance : MeasurableSpace (Lp E 2 μ) := borel _
local instance : BorelSpace (Lp E 2 μ) := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (Lp E 2 μ) := Lp.SecondCountableTopology

def good : Set ℝ≥0 := {t | MemLp (fun ω => f (t,ω)) 2 μ}

include hf in
theorem good_measurable : MeasurableSet (good μ f) := by
  have he : good μ f={t | Integrable (fun ω => ‖f (t,ω)‖^2) μ} := by
    ext t
    exact memLp_two_iff_integrable_sq_norm
      ((hf.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable)
  rw [he]
  exact measurableSet_integrable (hf.stronglyMeasurable.norm.pow 2)

def raw (p : ℝ≥0 × Ω) : E := by
  classical
  exact if p.1∈good μ f then f p else 0

include hf in
theorem raw_measurable : Measurable (raw μ f) :=
  Measurable.ite ((good_measurable μ f hf).preimage measurable_fst) hf measurable_const

theorem sections (t : ℝ≥0) : MemLp (fun ω => raw μ f (t,ω)) 2 μ := by
  by_cases ht : t∈good μ f
  · have hh : MemLp (fun ω => f (t,ω)) 2 μ := ht
    simpa only [raw,if_pos ht] using hh
  · simpa only [raw,if_neg ht] using (memLp_const (0:E) : MemLp (fun _ : Ω => (0:E)) 2 μ)

def value (t : ℝ≥0) : Lp E 2 μ := (sections μ f t).toLp (fun ω => raw μ f (t,ω))

theorem value_raw_ae (t : ℝ≥0) : value μ f t=ᵐ[μ] fun ω => raw μ f (t,ω) :=
  (sections μ f t).coeFn_toLp

include hf in
theorem measurable : Measurable (value μ f) :=
  SHEStochastic.MeasurableHilbertL2Realization.measurable (raw μ f) (raw_measurable μ f hf)
    (value μ f) (value_raw_ae μ f)

include hf in
theorem value_ae (H : ℝ≥0) (hfm : MemLp f 2 (energyMeasure μ H)) :
    ∀ᵐ t ∂timeMeasure H, value μ f t=ᵐ[μ] fun ω => f (t,ω) := by
  filter_upwards [hfm.norm.integrable_sq.prod_right_ae] with t ht
  have hgood : t∈good μ f := (memLp_two_iff_integrable_sq_norm
    ((hf.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable)).mpr ht
  simpa only [raw,if_pos hgood] using value_raw_ae μ f t

include hf in
theorem norm_sq_ae (H : ℝ≥0) (hfm : MemLp f 2 (energyMeasure μ H)) :
    (fun t => ‖value μ f t‖^2)=ᵐ[timeMeasure H] fun t => ∫ ω,‖f (t,ω)‖^2 ∂μ := by
  filter_upwards [value_ae μ f hf H hfm] with t ht
  rw [realLp_norm_sq]
  exact integral_congr_ae (ht.fun_comp (fun x : E => ‖x‖^2))

include hf in
theorem square_integrable (H : ℝ≥0) (hfm : MemLp f 2 (energyMeasure μ H)) :
    MemLp (value μ f) 2 (timeMeasure H) := by
  apply (memLp_two_iff_integrable_sq_norm (measurable μ f hf).stronglyMeasurable.aestronglyMeasurable).mpr
  exact hfm.norm.integrable_sq.integral_prod_left.congr (norm_sq_ae μ f hf H hfm).symm

include hf in
theorem energy (H : ℝ≥0) (hfm : MemLp f 2 (energyMeasure μ H)) :
    (∫ t,‖value μ f t‖^2 ∂timeMeasure H)=∫ p,‖f p‖^2 ∂energyMeasure μ H := by
  rw [integral_congr_ae (norm_sq_ae μ f hf H hfm)]
  exact (integral_prod _ hfm.norm.integrable_sq).symm

end HeatTimeLpField
#check @HeatTimeLpField.good_measurable
#print axioms HeatTimeLpField.good_measurable
#check @HeatTimeLpField.raw_measurable
#print axioms HeatTimeLpField.raw_measurable
#check @HeatTimeLpField.sections
#print axioms HeatTimeLpField.sections
#check @HeatTimeLpField.value_raw_ae
#print axioms HeatTimeLpField.value_raw_ae
#check @HeatTimeLpField.measurable
#print axioms HeatTimeLpField.measurable
#check @HeatTimeLpField.value_ae
#print axioms HeatTimeLpField.value_ae
#check @HeatTimeLpField.norm_sq_ae
#print axioms HeatTimeLpField.norm_sq_ae
#check @HeatTimeLpField.square_integrable
#print axioms HeatTimeLpField.square_integrable
#check @HeatTimeLpField.energy
#print HeatTimeLpField.energy
#print axioms HeatTimeLpField.energy
