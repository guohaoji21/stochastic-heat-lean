import HeatWeightedCellInput
import HeatIntervalCovariance
import SHE.ProcessEnergy
import HeatPastPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatWeightedCellEnergy
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  {a c : ℝ≥0} (hac : a≤c) (hcH : c≤H) (ζ : Ω → ℝ)
  (hζ : StronglyMeasurable[F a] ζ) (hζ2 : MemLp ζ 2 μ)

include hac hcH in
theorem norm_sq (x : E) :
    ‖HeatWeightedCellInput.constant F μ H a c ζ hζ hζ2 x‖^2=
      ((c:ℝ)-(a:ℝ))*(∫ ω,ζ ω^2 ∂μ)*‖x‖^2 := by
  rw [subsigma_norm_sq]
  have hraw : (fun p : ℝ≥0 × Ω => ‖HeatWeightedCellInput.constant F μ H a c ζ hζ hζ2 x p‖^2)=ᵐ[energyMeasure μ H]
      fun p => ((Ioc a c).indicator (fun _ => (1:ℝ)) p.1)*(ζ p.2)^2*‖x‖^2 := by
    filter_upwards [HeatWeightedCellInput.constant_ae F μ H a c ζ hζ hζ2 x] with p hp
    rw [hp]
    by_cases h : p.1∈Ioc a c
    · simp [PredictableSteps.step,h,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    · simp [PredictableSteps.step,h]
  rw [integral_congr_ae hraw]
  change (∫ p,((Ioc a c).indicator (fun _ => (1:ℝ)) p.1)*ζ p.2^2*‖x‖^2 ∂(timeMeasure H).prod μ)=_
  rw [integral_mul_const,integral_prod_mul (μ := timeMeasure H) (ν := μ)
    ((Ioc a c).indicator (fun _ => (1:ℝ))) (fun ω => ζ ω^2),integral_indicator measurableSet_Ioc,
    timeMeasure_restrict_Ioc a hcH,HeatIntervalCovariance.interval_integral]
  have hreal : (a:ℝ)≤(c:ℝ) := by exact_mod_cast hac
  simp only [integral_const,measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le hreal,smul_eq_mul,mul_one]

theorem post_eq (x : E) :
    PastItoInputs.post F μ H a (HeatWeightedCellInput.constant F μ H a c ζ hζ hζ2 x)=
      HeatWeightedCellInput.constant F μ H a c ζ hζ hζ2 x := by
  apply SHE.PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [PastItoInputs.post_ae F μ H a (HeatWeightedCellInput.constant F μ H a c ζ hζ hζ2 x),
    HeatWeightedCellInput.constant_ae F μ H a c ζ hζ hζ2 x] with p hp he
  rw [hp]
  by_cases ha : a<p.1
  · rw [if_pos ha]
  · rw [if_neg ha,he]
    have hn : p.1∉Ioc a c := fun h => ha h.1
    simp [PredictableSteps.step,hn]

end HeatWeightedCellEnergy
#check @HeatWeightedCellEnergy.norm_sq
#print HeatWeightedCellEnergy.norm_sq
#print axioms HeatWeightedCellEnergy.norm_sq
#check @HeatWeightedCellEnergy.post_eq
#print axioms HeatWeightedCellEnergy.post_eq
