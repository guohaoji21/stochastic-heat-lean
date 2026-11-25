import HeatControlConvolution

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatControlAdapted
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 → Ω → E) (hU : IsStronglyProgressive F U)

include hU hS hcontr in
theorem raw_past (t : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ≥0).prod (F t)]
      (HeatControlConvolution.raw S (Function.uncurry U) t) := by
  have hprog := hU t
  let R := HeatControlConvolution.raw S (Function.uncurry U) t
  letI : MeasurableSpace Ω := F t
  have hclock : Measurable (fun p : ℝ≥0 × Ω => (⟨min p.1 t,min_le_right p.1 t⟩ : Set.Iic t)) :=
    (measurable_fst.min measurable_const).subtype_mk
  have hf : StronglyMeasurable (fun p : ℝ≥0 × Ω => U (min p.1 t) p.2) :=
    hprog.comp_measurable (hclock.prodMk measurable_snd)
  have ht : Measurable (fun p : ℝ≥0 × Ω => t-p.1) := measurable_const.sub measurable_fst
  have ha : StronglyMeasurable (fun p : ℝ≥0 × Ω => S (t-p.1) (U (min p.1 t) p.2)) :=
    (HeatPredictableSemigroup.continuous_action S hS hcontr).comp_stronglyMeasurable
      (ht.stronglyMeasurable.prodMk hf)
  have he : R=(fun p : ℝ≥0 × Ω => if p.1<t then S (t-p.1) (U (min p.1 t) p.2) else 0) := by
    funext p
    by_cases h : p.1<t
    · simp only [R,HeatControlConvolution.raw,HeatVolterraKernel.raw,if_pos h,
        ContinuousLinearMap.id_apply,min_eq_left h.le]
      rfl
    · simp only [R,HeatControlConvolution.raw,HeatVolterraKernel.raw,if_neg h]
  change StronglyMeasurable R
  rw [he]
  exact (Measurable.ite (measurableSet_lt measurable_fst measurable_const) ha.measurable measurable_const).stronglyMeasurable

include hU hS hcontr in
theorem adapted (H t : ℝ≥0) : StronglyMeasurable[F t]
    (HeatControlConvolution.value H S (Function.uncurry U) t) := by
  have hr := raw_past S hS hcontr F U hU t
  letI : MeasurableSpace Ω := F t
  exact hr.integral_prod_left'

def clamp (H : ℝ≥0) : ℝ≥0 × Ω → E := fun p => U (min p.1 H) p.2

include hU in
theorem clamp_measurable (H : ℝ≥0) : StronglyMeasurable (clamp U H) := by
  have hclock : @Measurable (ℝ≥0 × Ω) (Set.Iic H)
      ((inferInstance : MeasurableSpace ℝ≥0).prod (F H)) _
      (fun p => ⟨min p.1 H,min_le_right p.1 H⟩) :=
    (measurable_fst.min measurable_const).subtype_mk
  have hh := (hU H).comp_measurable (hclock.prodMk (@measurable_snd ℝ≥0 Ω _ (F H)))
  apply hh.mono
  change MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ≥0) ⊔ MeasurableSpace.comap Prod.snd (F H) ≤
    MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ≥0) ⊔ MeasurableSpace.comap Prod.snd ‹MeasurableSpace Ω›
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le H))


include hU in
theorem clamp_progressive (H : ℝ≥0) : IsStronglyProgressive F (fun t ω => clamp U H (t,ω)) := by
  intro a
  have ht : @Measurable (Set.Iic a × Ω) (Set.Iic a)
      (Subtype.instMeasurableSpace.prod (F a)) _
      (fun p : Set.Iic a × Ω => ⟨min (p.1:ℝ≥0) H,show min (p.1:ℝ≥0) H≤a from (min_le_left _ _).trans p.1.property⟩) :=
    ((measurable_subtype_coe.comp measurable_fst).min measurable_const).subtype_mk
  exact (hU a).comp_measurable (ht.prodMk (@measurable_snd (Set.Iic a) Ω _ (F a)))

end HeatControlAdapted
#check @HeatControlAdapted.raw_past
#print axioms HeatControlAdapted.raw_past
#check @HeatControlAdapted.adapted
#print axioms HeatControlAdapted.adapted
#check @HeatControlAdapted.clamp_measurable
#print axioms HeatControlAdapted.clamp_measurable
#check @HeatControlAdapted.clamp_progressive
#print axioms HeatControlAdapted.clamp_progressive
