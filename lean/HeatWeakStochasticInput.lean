import HeatProjectedSliceFubini
import HeatWeakRawIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatWeakStochasticInput
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base)

def noise (u : Process (E := Base) F μ H) : Process (E := Base) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (M.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u

theorem noise_ae (u : Process (E := Base) F μ H) :
    noise F μ H M u=ᵐ[energyMeasure μ H] fun p => M (u p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ae_eq_of_ae_eq_trim (M.coeFn_compLpL u)

theorem input_identity (u : Process (E := Base) F μ H) (φ ψ : Base)
    (hφ : weakLaplacian φ ψ) (T : ℝ≥0) :
    (∫ t,HeatProjectedSliceFubini.projectMap F μ H (innerSL ℝ ψ)
      (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u) ∂timeMeasure T)=
      HeatProjectedSliceFubini.projectMap F μ H (innerSL ℝ φ)
        (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M T u)-
      HeatProjectedSliceFubini.projectMap F μ H (innerSL ℝ φ)
        (StoppedItoInputs.stop F μ H T (noise F μ H M u)) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [HeatProjectedSliceFubini.integral_ae F μ H family family_continuous family_contraction M (innerSL ℝ ψ) u T,
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub
      (HeatProjectedSliceFubini.projectMap F μ H (innerSL ℝ φ) (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M T u))
      (HeatProjectedSliceFubini.projectMap F μ H (innerSL ℝ φ) (StoppedItoInputs.stop F μ H T (noise F μ H M u)))),
    HeatHilbertRandomStop.project_ae F μ H (innerSL ℝ φ) (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M T u),
    HeatHilbertRandomStop.project_ae F μ H (innerSL ℝ φ) (StoppedItoInputs.stop F μ H T (noise F μ H M u)),
    HeatVolterraSlice.slice_ae F μ H family family_continuous family_contraction M T u,
    StoppedItoInputs.stop_ae F μ H T (noise F μ H M u),noise_ae F μ H M u] with p hl hd h1 h2 hs hstop hnoise
  rw [hl,hd]
  simp only [Pi.sub_apply,HeatProjectedSliceFubini.projectMap_apply]
  rw [h1,h2,hs,hstop]
  change (∫ t,HeatUnitHilbertColumns.columnEquiv (inner ℝ ψ (HeatVolterraKernel.raw family M u (t,p))) ∂timeMeasure T)=
    HeatUnitHilbertColumns.columnEquiv (inner ℝ φ (HeatVolterraKernel.raw family M u (T,p)))-
      HeatUnitHilbertColumns.columnEquiv (inner ℝ φ ((StoppedItoInputs.before (T:ℝ)).indicator (noise F μ H M u) p))
  have hc := HeatUnitHilbertColumns.columnEquiv.toLinearIsometry.integral_comp_comm (μ := timeMeasure T)
    (fun t => inner ℝ ψ (HeatVolterraKernel.raw family M u (t,p)))
  change (∫ t,HeatUnitHilbertColumns.columnEquiv (inner ℝ ψ (HeatVolterraKernel.raw family M u (t,p))) ∂timeMeasure T)=
    HeatUnitHilbertColumns.columnEquiv (∫ t,inner ℝ ψ (HeatVolterraKernel.raw family M u (t,p)) ∂timeMeasure T) at hc
  rw [hc,HeatWeakRawIntegral.integral_raw u M φ ψ hφ T p,map_sub]
  by_cases hp : p.1<T
  · rw [if_pos hp,Set.indicator_of_mem (show p∈StoppedItoInputs.before (T:ℝ) from hp),hnoise]
  · rw [if_neg hp,Set.indicator_of_notMem (show p∉StoppedItoInputs.before (T:ℝ) from hp)]
    simp only [inner_zero_right]

end HeatWeakStochasticInput
#check @HeatWeakStochasticInput.noise_ae
#print axioms HeatWeakStochasticInput.noise_ae
#check @HeatWeakStochasticInput.input_identity
#print HeatWeakStochasticInput.input_identity
#print axioms HeatWeakStochasticInput.input_identity
