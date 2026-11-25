import SHE.PredictableTime
import HeatPathMaximum
import SHE.PredictableL2
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatPathObservation
open MeasureTheory Set SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure Ω) (H : ℝ≥0) (X : ℝ≥0 → Ω → E)

theorem norm_le_max (hc : ∀ ω,Continuous (fun s => X s ω))
    {s : ℝ≥0} (hs : s ≤ H) (ω : Ω) : ‖X s ω‖ ≤ HeatPathMaximum.value H X ω := by
  have hcomp : IsCompact (Iic H : Set ℝ≥0) := by
    convert isCompact_Icc (a := (0:ℝ≥0)) (b := H) using 1
    ext x
    simp
  obtain ⟨t,ht,hmax⟩ := hcomp.exists_isMaxOn ⟨0,by simp⟩ (hc ω).norm.continuousOn
  have hsup : (⨆ u : Iic H,‖X u ω‖ₑ) ≤ ENNReal.ofReal ‖X t ω‖ := by
    apply iSup_le
    intro u
    rw [←ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hmax u.property)
  have hfin : (⨆ u : Iic H,‖X u ω‖ₑ)≠⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup
  have hh := ENNReal.toReal_mono hfin (le_iSup (fun u : Iic H => ‖X u ω‖ₑ) ⟨s,hs⟩)
  simpa only [HeatPathMaximum.value,←ofReal_norm,ENNReal.toReal_ofReal (norm_nonneg _)] using hh

theorem integrable [SFinite μ] (hc : ∀ ω,Continuous (fun s => X s ω))
    (hm : StronglyMeasurable (Function.uncurry X))
    (hmax : Integrable (fun ω => HeatPathMaximum.value H X ω^2) μ)
    (L : E →L[ℝ] V) : Integrable (fun p : ℝ≥0 × Ω => ‖L (X p.1 p.2)‖^2) (energyMeasure μ H) := by
  have hD := (hmax.comp_snd (timeMeasure H)).const_mul (‖L‖^2)
  have hstrong : StronglyMeasurable (fun p : ℝ≥0 × Ω => ‖L (X p.1 p.2)‖^2) :=
    ((L.continuous.comp_stronglyMeasurable hm).norm).pow 2
  apply hD.mono' hstrong.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hbound := norm_le_max H X hc hp.2 p.2
  have hLm : ‖L (X p.1 p.2)‖ ≤ ‖L‖*HeatPathMaximum.value H X p.2 :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hbound (norm_nonneg _))
  calc
    _ ≤ (‖L‖*HeatPathMaximum.value H X p.2)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hLm 2
    _ = _ := mul_pow _ _ _

end HeatPathObservation
#check @HeatPathObservation.norm_le_max
#print axioms HeatPathObservation.norm_le_max
#check @HeatPathObservation.integrable
#print axioms HeatPathObservation.integrable
