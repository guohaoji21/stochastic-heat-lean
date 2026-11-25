import HeatTorusFiniteHeatGenerator
import HeatSliceNorm
import SHE.TerminalItoFubini

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace HeatTorusFiniteStochasticAdditive

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.HilbertColumns
open HeatTorusGalerkinBackward (State laplace)
open HeatTorusProjectedConvolution (finiteHeat finiteHeat_continuous finiteHeat_contraction)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {Ω κ : Type*} [mΩ : MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : Finset (ι → ℤ)) (P : ℝ)

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

local notation "ν" => Measure.trim (energyMeasure μ H) (predictable_le_product F)
local notation "U" => HeatVolterraSlice.slice F μ H (finiteHeat S P) (finiteHeat_continuous S P)
    (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S))

theorem kernel_primitive (v : ℝ≥0 × Ω → State S) (t : ℝ≥0) (p : ℝ≥0 × Ω) :
    (∫ r, laplace S P (HeatVolterraKernel.raw (finiteHeat S P)
      (ContinuousLinearMap.id ℝ (State S)) v (r, p)) ∂timeMeasure t) =
      HeatVolterraKernel.raw (finiteHeat S P) (ContinuousLinearMap.id ℝ (State S)) v (t, p) -
        (before (t : ℝ)).indicator v p := by
  classical
  by_cases hp : p.1 < t
  · have he : (fun r => laplace S P (HeatVolterraKernel.raw (finiteHeat S P)
        (ContinuousLinearMap.id ℝ (State S)) v (r, p))) =ᵐ[timeMeasure t]
        (Ioc p.1 t).indicator (fun r => laplace S P (finiteHeat S P (r - p.1) (v p))) := by
      filter_upwards [timeMeasure_ae_mem t] with r hr
      by_cases hpr : p.1 < r
      · rw [indicator_of_mem (show r ∈ Ioc p.1 t from ⟨hpr, hr.2⟩)]
        simp only [HeatVolterraKernel.raw, ite_eq_left hpr, ContinuousLinearMap.id_apply]
      · rw [indicator_of_notMem (show r ∉ Ioc p.1 t from fun h => hpr h.1)]
        simp only [HeatVolterraKernel.raw, ite_eq_right hpr, map_zero]
    rw [integral_congr_ae he, integral_indicator measurableSet_Ioc]
    rw [HeatTorusFiniteHeatGenerator.integrated_shift S P hp.le]
    simp only [HeatVolterraKernel.raw, ite_eq_left hp, ContinuousLinearMap.id_apply,
      indicator_of_mem (show p ∈ before (t : ℝ) from hp)]
  · have he : (fun r => laplace S P (HeatVolterraKernel.raw (finiteHeat S P)
        (ContinuousLinearMap.id ℝ (State S)) v (r, p))) =ᵐ[timeMeasure t] 0 := by
      filter_upwards [timeMeasure_ae_mem t] with r hr
      have hpr : ¬ p.1 < r := fun h => hp (h.trans_le hr.2)
      simp only [HeatVolterraKernel.raw, ite_eq_right hpr, map_zero, Pi.zero_apply]
    rw [integral_congr_ae he]
    simp only [Pi.zero_apply, integral_zero, HeatVolterraKernel.raw, ite_eq_right hp,
      indicator_of_notMem (show p ∉ before (t : ℝ) from hp), sub_zero]

/-- The Galerkin convolution integrand satisfies the integrated generator
identity in the original predictable L² space. -/
theorem input_integral (v : Process (E := State S) F μ H) (t : ℝ≥0) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    (∫ r, ((laplace S P).compLpL 2 ν) (U r v) ∂timeMeasure t) = U t v - stop F μ H t v := by
  let A := laplace S P
  let B := ambientIsometry (E := State S) (energyMeasure μ H) (predictable_le_product F)
  let K (r : ℝ≥0) : Process (E := State S) F μ H := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (A.compLpL 2 ν) (U r v)
  change (∫ r, K r ∂timeMeasure t) = U t v - stop F μ H t v
  let raw : ℝ≥0 × (ℝ≥0 × Ω) → State S := fun p =>
    A (HeatVolterraKernel.raw (finiteHeat S P) (ContinuousLinearMap.id ℝ (State S)) v p)
  have hK : Integrable K (timeMeasure t) := by
    let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (A.compLpL 2 ν).integrable_comp
      (HeatSliceNorm.integrable F μ H (finiteHeat S P) (finiteHeat_continuous S P)
        (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) v t)
  let : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  have hv : Measurable (v : ℝ≥0 × Ω → State S) :=
    ((Lp.stronglyMeasurable v).mono (predictable_le_product F)).measurable
  have hraw : Measurable raw := A.continuous.measurable.comp
    (HeatVolterraKernel.raw_measurable (finiteHeat S P) (ContinuousLinearMap.id ℝ (State S))
      (finiteHeat_continuous S P) (finiteHeat_contraction S P) v hv)
  have hvi : Integrable (v : ℝ≥0 × Ω → State S) (energyMeasure μ H) :=
    (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)).integrable one_le_two
  have hri : Integrable raw ((timeMeasure t).prod (energyMeasure μ H)) := by
    apply ((hvi.norm.comp_snd (timeMeasure t)).const_mul ‖A‖).mono' hraw.stronglyMeasurable.aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    refine (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    by_cases hp : p.2.1 < p.1
    · simpa only [HeatVolterraKernel.raw, ite_eq_left hp, ContinuousLinearMap.id_apply] using
        finiteHeat_contraction S P (p.1 - p.2.1) (v p.2)
    · simp only [HeatVolterraKernel.raw, ite_eq_right hp, norm_zero, norm_nonneg]
  have hrep : ∀ᵐ r ∂timeMeasure t, (B (K r) : ℝ≥0 × Ω → State S) =ᵐ[energyMeasure μ H]
      fun p => raw (r, p) := by
    apply Eventually.of_forall
    intro r
    have hKa : (K r : ℝ≥0 × Ω → State S) =ᵐ[energyMeasure μ H] fun p => A (U r v p) := by
      let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      exact ae_eq_of_ae_eq_trim (A.coeFn_compLpL (U r v))
    filter_upwards [ambient_ae (energyMeasure μ H) (predictable_le_product F) (K r),
      hKa,
      HeatVolterraSlice.slice_ae F μ H (finiteHeat S P) (finiteHeat_continuous S P)
        (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) r v] with p hb ha hu
    change B (K r) p = K r p at hb
    change K r p = A (U r v p) at ha
    rw [hb, ha, hu]
  have hr := SHE.LpIntegralFubini.integral_ae (energyMeasure μ H) (timeMeasure t)
    (fun r => B (K r)) (B.toContinuousLinearMap.integrable_comp hK) raw hri hrep
  have hc := B.integral_comp_comm (μ := timeMeasure t) K
  change (∫ r, B (K r) ∂timeMeasure t) = B (∫ r, K r ∂timeMeasure t) at hc
  rw [hc] at hr
  change (∫ r, K r ∂timeMeasure t) = U t v - stop F μ H t v
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ambient_ae (energyMeasure μ H) (predictable_le_product F) (∫ r, K r ∂timeMeasure t),
    hr, ae_eq_of_ae_eq_trim (Lp.coeFn_sub (U t v) (stop F μ H t v)),
    HeatVolterraSlice.slice_ae F μ H (finiteHeat S P) (finiteHeat_continuous S P)
      (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) t v,
    stop_ae F μ H t v] with p ha hr hsub hu hv
  change B (∫ r, K r ∂timeMeasure t) p = (∫ r, K r ∂timeMeasure t : Process F μ H) p at ha
  rw [← ha, hr, hsub, Pi.sub_apply, hu, hv]
  exact kernel_primitive S P v t p

/-- The finite stochastic heat convolution is the stopped Itô integral
plus the time integral of the Galerkin Laplacian acting on that convolution. -/
theorem additive (b : HilbertBasis κ ℝ (State S))
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (v : Process (E := State S) F μ H) (t : ℝ≥0) :
    let I := HeatTerminalNaturality.integral F μ H b J
    I.integral (U t v) = I.integral (stop F μ H t v) +
      ∫ r, ((laplace S P).compLpL 2 μ) (I.integral (U r v)) ∂timeMeasure t := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  intro I
  have h := congrArg I.integral (input_integral F μ H S P v t)
  change I.integral (∫ r, ((laplace S P).compLpL 2 ν) (U r v) ∂timeMeasure t) = _ at h
  rw [TerminalItoFubini.integral_comm, map_sub] at h
  have hnat (r : ℝ≥0) : I.integral (((laplace S P).compLpL 2 ν) (U r v)) =
      ((laplace S P).compLpL 2 μ) (I.integral (U r v)) :=
    (HeatTerminalNaturality.commutes F μ H b J (laplace S P) (U r v)).symm
  simp_rw [hnat] at h
  rw [h]
  abel

end HeatTorusFiniteStochasticAdditive

#print axioms HeatTorusFiniteStochasticAdditive.input_integral
#print axioms HeatTorusFiniteStochasticAdditive.additive
