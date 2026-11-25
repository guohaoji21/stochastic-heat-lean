import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
noncomputable section
namespace HeatRestrictionAdjoint
open MeasureTheory
open scoped NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X)

def restrictLinear : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 (μ.restrict s) where
  toFun f := ((Lp.memLp f).restrict s).toLp f
  map_add' f g := Lp_toLp_restrict_add f g s
  map_smul' c f := Lp_toLp_restrict_smul c f s

def restriction : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict s) :=
  (restrictLinear μ s).mkContinuous 1 (fun f => by
    change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_Lp_toLp_restrict_le s f)

theorem restriction_ae (f : Lp ℝ 2 μ) :
    (restriction μ s f : X → ℝ) =ᵐ[μ.restrict s] f :=
  ((Lp.memLp f).restrict s).coeFn_toLp

def adjointExtension : Lp ℝ 2 (μ.restrict s) →L[ℝ] Lp ℝ 2 μ :=
  (restriction μ s).adjoint

theorem restriction_adjoint_pairing (f : Lp ℝ 2 μ) (g : Lp ℝ 2 (μ.restrict s)) :
    inner ℝ (restriction μ s f) g = inner ℝ f (adjointExtension μ s g) := by
  exact ((restriction μ s).adjoint_inner_right f g).symm


theorem adjointExtension_ae (hs : MeasurableSet s) (g : Lp ℝ 2 (μ.restrict s)) :
    (adjointExtension μ s g : X → ℝ) =ᵐ[μ] s.indicator g := by
  have hm : MemLp (s.indicator g) 2 μ :=
    (memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (Lp.memLp g)
  let w : Lp ℝ 2 μ := hm.toLp _
  have hw : adjointExtension μ s g = w := by
    apply ext_inner_left ℝ
    intro f
    rw [← restriction_adjoint_pairing μ s f g, L2.inner_def, L2.inner_def]
    rw [← integral_indicator hs]
    apply integral_congr_ae
    have hr := (ae_restrict_iff' hs).mp (restriction_ae μ s f)
    filter_upwards [hr,hm.coeFn_toLp] with x hr hx
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs,hr hxs,hx,Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem hxs,hx,Set.indicator_of_notMem hxs]
      simp
  rw [hw]
  exact hm.coeFn_toLp


def paperDomainMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 10)
def paperControlMeasure : Measure ℝ := paperDomainMeasure.restrict (Set.Ioo (1 : ℝ) 2)

theorem paper_control_measure :
    paperControlMeasure = volume.restrict (Set.Ioo (1 : ℝ) 2) := by
  unfold paperControlMeasure paperDomainMeasure
  apply Measure.restrict_restrict_of_subset
  intro x hx
  simp only [Set.mem_Ioo] at hx ⊢
  constructor <;> linarith

def paperBstar : Lp ℝ 2 paperDomainMeasure →L[ℝ] Lp ℝ 2 paperControlMeasure :=
  restriction paperDomainMeasure (Set.Ioo (1 : ℝ) 2)

def paperB : Lp ℝ 2 paperControlMeasure →L[ℝ] Lp ℝ 2 paperDomainMeasure :=
  adjointExtension paperDomainMeasure (Set.Ioo (1 : ℝ) 2)

theorem paperB_is_zero_extension (g : Lp ℝ 2 paperControlMeasure) :
    (paperB g : ℝ → ℝ) =ᵐ[paperDomainMeasure] (Set.Ioo (1 : ℝ) 2).indicator g :=
  adjointExtension_ae paperDomainMeasure (Set.Ioo (1 : ℝ) 2) measurableSet_Ioo g

theorem paperBstar_is_restriction (f : Lp ℝ 2 paperDomainMeasure) :
    (paperBstar f : ℝ → ℝ) =ᵐ[paperControlMeasure] f :=
  restriction_ae paperDomainMeasure (Set.Ioo (1 : ℝ) 2) f

theorem paperB_adjoint : paperB.adjoint = paperBstar := by
  change (restriction paperDomainMeasure (Set.Ioo (1 : ℝ) 2)).adjoint.adjoint =
    restriction paperDomainMeasure (Set.Ioo (1 : ℝ) 2)
  exact ContinuousLinearMap.adjoint_adjoint _

end HeatRestrictionAdjoint
#check @HeatRestrictionAdjoint.restriction_ae
#print axioms HeatRestrictionAdjoint.restriction_ae
#check @HeatRestrictionAdjoint.restriction_adjoint_pairing
#print axioms HeatRestrictionAdjoint.restriction_adjoint_pairing

#check @HeatRestrictionAdjoint.adjointExtension_ae
#print axioms HeatRestrictionAdjoint.adjointExtension_ae

#check @HeatRestrictionAdjoint.paper_control_measure
#print axioms HeatRestrictionAdjoint.paper_control_measure
#check @HeatRestrictionAdjoint.paperB_is_zero_extension
#print axioms HeatRestrictionAdjoint.paperB_is_zero_extension
#check @HeatRestrictionAdjoint.paperBstar_is_restriction
#print axioms HeatRestrictionAdjoint.paperBstar_is_restriction
#check @HeatRestrictionAdjoint.paperB_adjoint
#print axioms HeatRestrictionAdjoint.paperB_adjoint
