import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatDeterministicPairing
open MeasureTheory Filter Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ν : Measure ℝ≥0) [IsFiniteMeasure ν] [NullSingletonClass ν]

def cumulative (f : ℝ≥0 → E) (t : ℝ≥0) : E := ∫ s in Iio t, f s ∂ν

theorem product_integrable (f g : ℝ≥0 → E) (hf : Integrable f ν) (hg : Integrable g ν) :
    Integrable (fun p : ℝ≥0 × ℝ≥0 => inner ℝ (f p.1) (g p.2)) (ν.prod ν) := by
  apply (hf.norm.mul_prod hg.norm).mono'
  · exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).inner
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  · exact Filter.Eventually.of_forall (fun p => norm_inner_le_norm _ _)

theorem cumulative_integrable (f : ℝ≥0 → E) (hf : Integrable f ν) :
    Integrable (cumulative ν f) ν := by
  have hi : Integrable (fun p : ℝ≥0 × ℝ≥0 =>
      ({q : ℝ≥0 × ℝ≥0 | q.2<q.1}.indicator (fun q => f q.2)) p) (ν.prod ν) :=
    (hf.comp_snd ν).indicator (measurableSet_lt measurable_snd measurable_fst)
  apply hi.integral_prod_left.congr
  exact Filter.Eventually.of_forall (fun t => by
    change (∫ s, (Iio t).indicator f s ∂ν)=_
    rw [integral_indicator measurableSet_Iio]
    rfl)

theorem product_rule (f g : ℝ≥0 → E) (hf : Integrable f ν) (hg : Integrable g ν) :
    inner ℝ (∫ s, f s ∂ν) (∫ s, g s ∂ν)=
      (∫ s, inner ℝ (f s) (cumulative ν g s) ∂ν)+
      (∫ s, inner ℝ (cumulative ν f s) (g s) ∂ν) := by
  let h : ℝ≥0 × ℝ≥0 → ℝ := fun p => inner ℝ (f p.1) (g p.2)
  let A : Set (ℝ≥0 × ℝ≥0) := {p | p.2<p.1}
  let B : Set (ℝ≥0 × ℝ≥0) := {p | p.1<p.2}
  have hmA : MeasurableSet A := measurableSet_lt measurable_snd measurable_fst
  have hmB : MeasurableSet B := measurableSet_lt measurable_fst measurable_snd
  have hi : Integrable h (ν.prod ν) := product_integrable ν f g hf hg
  have hA := hi.indicator hmA
  have hB := hi.indicator hmB
  have hne : ∀ᵐ p ∂ν.prod ν, p.1≠p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    apply Filter.Eventually.of_forall
    intro s
    filter_upwards [ν.ae_ne s] with t ht using Ne.symm ht
  have he : h=ᵐ[ν.prod ν] A.indicator h+B.indicator h := by
    filter_upwards [hne] with p hp
    rcases lt_or_gt_of_ne hp with hl|hr
    · have hno : p ∉ A := not_lt.mpr hl.le
      have hy : p ∈ B := hl
      simp only [Pi.add_apply,indicator_of_notMem hno,indicator_of_mem hy,zero_add]
    · have hno : p ∉ B := not_lt.mpr hr.le
      have hy : p ∈ A := hr
      simp only [Pi.add_apply,indicator_of_mem hy,indicator_of_notMem hno,add_zero]
  have whole : (∫ p, h p ∂ν.prod ν)=inner ℝ (∫ s, f s ∂ν) (∫ s, g s ∂ν) := by
    exact integral_prod_bilin (innerSL ℝ) hf hg
  have left : (∫ p, A.indicator h p ∂ν.prod ν)=∫ s, inner ℝ (f s) (cumulative ν g s) ∂ν := by
    rw [integral_prod _ hA]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by
      change (∫ t, (Iio s).indicator (fun t => inner ℝ (f s) (g t)) t ∂ν)=_
      rw [integral_indicator measurableSet_Iio,integral_inner hg.restrict]
      rfl)
  have right : (∫ p, B.indicator h p ∂ν.prod ν)=∫ s, inner ℝ (cumulative ν f s) (g s) ∂ν := by
    rw [integral_prod_symm _ hB]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by
      change (∫ t, (Iio s).indicator (fun t => inner ℝ (f t) (g s)) t ∂ν)=_
      rw [integral_indicator measurableSet_Iio]
      rw [show (fun t => inner ℝ (f t) (g s))=(fun t => inner ℝ (g s) (f t)) from funext (fun t => real_inner_comm _ _)]
      rw [integral_inner hf.restrict,real_inner_comm]
      rfl)
  rw [← whole,integral_congr_ae he,integral_add' hA hB,left,right]

end HeatDeterministicPairing
#check @HeatDeterministicPairing.product_integrable
#print axioms HeatDeterministicPairing.product_integrable
#check @HeatDeterministicPairing.product_rule
#print axioms HeatDeterministicPairing.product_rule

#check @HeatDeterministicPairing.cumulative_integrable
#print axioms HeatDeterministicPairing.cumulative_integrable
