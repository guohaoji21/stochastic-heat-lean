import HeatControlAdapted

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatFiniteControlExtension
open MeasureTheory Filter Set SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (U : ℝ≥0 → Ω → E)

def LocallyProgressive : Prop := ∀ t : ℝ≥0, t≤H →
  StronglyMeasurable[(inferInstance : MeasurableSpace (Iic t)).prod (F t)]
    (fun p : Iic t × Ω => U p.1 p.2)

theorem extend (hU : LocallyProgressive F H U) :
    IsStronglyProgressive F (fun t ω => U (min t H) ω) := by
  intro a
  let b := min a H
  have hlocal := hU b (min_le_right a H)
  have hmono : (inferInstance : MeasurableSpace (Iic b)).prod (F b)≤
      (inferInstance : MeasurableSpace (Iic b)).prod (F a) := by
    change MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd (F b)≤
      MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd (F a)
    exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.mono (min_le_left a H)))
  have hlocal' := hlocal.mono hmono
  have hclock : @Measurable (Iic a × Ω) (Iic b)
      ((inferInstance : MeasurableSpace (Iic a)).prod (F a)) _
      (fun p : Iic a × Ω => ⟨min (p.1:ℝ≥0) H,min_le_min_right H p.1.property⟩) :=
    ((measurable_subtype_coe.comp measurable_fst).min measurable_const).subtype_mk
  exact hlocal'.comp_measurable (hclock.prodMk (@measurable_snd (Iic a) Ω _ (F a)))

theorem energy_ae : (fun p : ℝ≥0 × Ω => U (min p.1 H) p.2)=ᵐ[energyMeasure μ H] Function.uncurry U := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
  simp only [min_eq_left hp.2,Function.uncurry_apply_pair]
  rfl

end HeatFiniteControlExtension
#check @HeatFiniteControlExtension.extend
#print HeatFiniteControlExtension.extend
#print axioms HeatFiniteControlExtension.extend
#check @HeatFiniteControlExtension.energy_ae
#print axioms HeatFiniteControlExtension.energy_ae
