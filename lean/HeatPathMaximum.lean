import SHEStochastic.DoobL2Envelope

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatPathMaximum
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure Ω) (H : ℝ≥0) (X : ℝ≥0 → Ω → E)

def value (ω : Ω) : ℝ := (⨆ t : Iic H, ‖X t ω‖ₑ).toReal

theorem measurable (hx : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous (fun t => X t ω)) :
    Measurable (value H X) := by
  have he : (fun ω => ⨆ t : Iic H, ‖X t ω‖ₑ) = ⨆ t : Iic H, (fun ω => ‖X t ω‖ₑ) := by ext; simp
  apply Measurable.ennreal_toReal
  rw [he]
  apply measurable_iSup_of_rightContinuous
  · intro ω a
    exact ((hc ω).enorm.isRightContinuous a).comp continuous_subtype_val.continuousWithinAt (fun _ => by simp)
  · intro t
    exact (hx t).enorm

theorem memLp (hx : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous (fun t => X t ω))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ t, t ≤ H → ∀ ω, ‖X t ω‖ ≤ D ω) : MemLp (value H X) 2 μ := by
  have hA (ω : Ω) : (⨆ t : Iic H, ‖X t ω‖ₑ) ≤ ENNReal.ofReal (D ω) := by
    apply iSup_le
    intro t
    rw [←ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb t t.property ω)
  apply hD.mono' (measurable H X hx hc).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖(⨆ t : Iic H, ‖X t ω‖ₑ).toReal‖ ≤ D ω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hA ω)
  simpa only [ENNReal.toReal_ofReal (hD0 ω)] using hh

theorem attained (hc : ∀ ω, Continuous (fun t => X t ω)) (ω : Ω) :
    ∃ t : ℝ≥0, t ≤ H ∧ value H X ω = ‖X t ω‖ := by
  have hcomp : IsCompact (Iic H : Set ℝ≥0) := by
    convert isCompact_Icc (a := (0:ℝ≥0)) (b := H) using 1
    ext x
    simp
  obtain ⟨t,ht,hmax⟩ := hcomp.exists_isMaxOn ⟨0,by simp⟩ (hc ω).norm.continuousOn
  refine ⟨t,ht,?_⟩
  have he : (⨆ s : Iic H, ‖X s ω‖ₑ) = ‖X t ω‖ₑ := by
    apply le_antisymm
    · apply iSup_le
      intro s
      rw [←ofReal_norm,←ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hmax s.property)
    · exact le_iSup (fun s : Iic H => ‖X s ω‖ₑ) ⟨t,ht⟩
  unfold value
  rw [he,←ofReal_norm,ENNReal.toReal_ofReal (norm_nonneg _)]

theorem integrable_square (hx : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous (fun t => X t ω))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hb : ∀ t, t ≤ H → ∀ ω, ‖X t ω‖ ≤ D ω) :
    Integrable (fun ω => value H X ω^2) μ := by
  have hh := (memLp μ H X hx hc D hD hD0 hb).norm.integrable_sq
  simpa only [Real.norm_eq_abs,sq_abs] using hh

end HeatPathMaximum
#check @HeatPathMaximum.measurable
#print axioms HeatPathMaximum.measurable
#check @HeatPathMaximum.memLp
#print axioms HeatPathMaximum.memLp
#check @HeatPathMaximum.attained
#print axioms HeatPathMaximum.attained
#check @HeatPathMaximum.integrable_square
#print axioms HeatPathMaximum.integrable_square
