import HeatSliceNorm
import HeatHilbertRandomStop
import SHE.LpIntegralFubini

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatProjectedSliceFubini
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure;infer_instance

def projectMap (L : E →L[ℝ] ℝ) : Process (E := E) F μ H →L[ℝ] Process (E := Space Unit ℝ) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let ν := (energyMeasure μ H).trim (predictable_le_product F)
  exact (HeatUnitHilbertLp.lpEquiv ν).toLinearIsometry.toContinuousLinearMap.comp (L.compLpL 2 ν)

theorem projectMap_apply (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) :
    projectMap F μ H L u=HeatHilbertRandomStop.project F μ H L u := rfl

theorem integrable (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) (T : ℝ≥0) :
    Integrable (fun t => projectMap F μ H L (HeatVolterraSlice.slice F μ H S hS hcontr M t u)) (timeMeasure T) :=
  (projectMap F μ H L).integrable_comp (HeatSliceNorm.integrable F μ H S hS hcontr M u T)

theorem integral_ae (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) (T : ℝ≥0) :
    (∫ t,projectMap F μ H L (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ∂timeMeasure T)=ᵐ[energyMeasure μ H]
      fun p => ∫ t,HeatUnitHilbertColumns.columnEquiv (L (HeatVolterraKernel.raw S M u (t,p))) ∂timeMeasure T := by
  let A := ambientIsometry (E := Space Unit ℝ) (energyMeasure μ H) (predictable_le_product F)
  let K := fun t => projectMap F μ H L (HeatVolterraSlice.slice F μ H S hS hcontr M t u)
  let raw : ℝ≥0 × (ℝ≥0 × Ω) → Space Unit ℝ := fun p =>
    HeatUnitHilbertColumns.columnEquiv (L (HeatVolterraKernel.raw S M u p))
  have hum : Measurable (u : ℝ≥0 × Ω → E) :=
    ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
  have hrm : Measurable raw := HeatUnitHilbertColumns.columnEquiv.continuous.measurable.comp
    (L.continuous.measurable.comp (HeatVolterraKernel.raw_measurable S M hS hcontr u hum))
  have hui : Integrable (u : ℝ≥0 × Ω → E) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).integrable (by norm_num)
  have hri : Integrable raw ((timeMeasure T).prod (energyMeasure μ H)) := by
    apply ((hui.norm.comp_snd (timeMeasure T)).const_mul (‖L‖*‖M‖)).mono' hrm.stronglyMeasurable.aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    change ‖HeatUnitHilbertColumns.columnEquiv (L (HeatVolterraKernel.raw S M u p))‖≤(‖L‖*‖M‖)*‖u p.2‖
    rw [HeatUnitHilbertColumns.columnEquiv.norm_map]
    exact ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (HeatVolterraModel.raw_norm_bound F μ H S hS hcontr M u p) (norm_nonneg L))).trans_eq (mul_assoc _ _ _).symm
  have hrep : ∀ᵐ t ∂timeMeasure T, A (K t)=ᵐ[energyMeasure μ H] fun p => raw (t,p) := by
    apply Eventually.of_forall
    intro t
    filter_upwards [ambient_ae (energyMeasure μ H) (predictable_le_product F) (K t),
      HeatHilbertRandomStop.project_ae F μ H L (HeatVolterraSlice.slice F μ H S hS hcontr M t u),
      HeatVolterraSlice.slice_ae F μ H S hS hcontr M t u] with p ha hp hs
    change A (K t) p=K t p at ha
    change K t p=HeatUnitHilbertColumns.columnEquiv (L (HeatVolterraSlice.slice F μ H S hS hcontr M t u p)) at hp
    rw [ha,hp,hs]
  have hki : Integrable K (timeMeasure T) := integrable F μ H S hS hcontr M L u T
  have he := SHE.LpIntegralFubini.integral_ae (energyMeasure μ H) (timeMeasure T)
    (fun t => A (K t)) (A.toContinuousLinearMap.integrable_comp hki) raw hri hrep
  have hcomm := A.integral_comp_comm (μ := timeMeasure T) K
  change (∫ t,A (K t) ∂timeMeasure T)=A (∫ t,K t ∂timeMeasure T) at hcomm
  rw [hcomm] at he
  exact (ambient_ae (energyMeasure μ H) (predictable_le_product F) (∫ t,K t ∂timeMeasure T)).symm.trans he

end HeatProjectedSliceFubini
#check @HeatProjectedSliceFubini.projectMap_apply
#print axioms HeatProjectedSliceFubini.projectMap_apply
#check @HeatProjectedSliceFubini.integrable
#print axioms HeatProjectedSliceFubini.integrable
#check @HeatProjectedSliceFubini.integral_ae
#print HeatProjectedSliceFubini.integral_ae
#print axioms HeatProjectedSliceFubini.integral_ae
