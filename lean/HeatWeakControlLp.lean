import HeatWeakControlPath
import HeatAmbientDrift
import HeatCompactTimeIntegrability
import HeatControlJoint
import SHE.LpIntegralFubini

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatWeakControlLp
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatIntervalNormalization
open HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem weak_equation (f : ℝ≥0 × Ω → Base) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (Q : ℝ≥0 → Lp Base 2 μ) (hQc : Continuous Q)
    (hQr : ∀ t, Q t=ᵐ[μ] HeatControlConvolution.value H family f t)
    {T : ℝ≥0} (hT : T≤H)
    (hj : Integrable (fun p : ℝ≥0 × Ω => HeatControlConvolution.value H family f p.1 p.2) (energyMeasure μ T))
    (φ ψ : Base) (hφ : weakLaplacian φ ψ) :
    ((innerSL ℝ φ).compLpL 2 μ) (Q T)=
      ((innerSL ℝ φ).compLpL 2 μ) (HeatAmbientDrift.value μ H f hf hfm T)+
        ∫ t,((innerSL ℝ ψ).compLpL 2 μ) (Q t) ∂timeMeasure T := by
  let P := (innerSL ℝ ψ).compLpL 2 μ
  have hPi : Integrable (fun t => P (Q t)) (timeMeasure T) :=
    HeatCompactTimeIntegrability.of_continuous _ (P.continuous.comp hQc) T
  have hrep : ∀ᵐ t ∂timeMeasure T, P (Q t)=ᵐ[μ] fun ω => inner ℝ ψ (HeatControlConvolution.value H family f t ω) := by
    apply Eventually.of_forall
    intro t
    filter_upwards [(innerSL ℝ ψ).coeFn_compLpL (Q t),hQr t] with ω hp hq
    change P (Q t) ω=_ at hp
    exact hp.trans (congrArg (innerSL ℝ ψ) hq)
  have hInt := SHE.LpIntegralFubini.integral_ae μ (timeMeasure T) (fun t => P (Q t)) hPi
    (fun p : ℝ≥0 × Ω => inner ℝ ψ (HeatControlConvolution.value H family f p.1 p.2)) (hj.const_inner ψ) hrep
  apply Lp.ext
  filter_upwards [(innerSL ℝ φ).coeFn_compLpL (Q T),hQr T,
    HeatAmbientDrift.value_ae μ H f hf hfm hT,
    (innerSL ℝ φ).coeFn_compLpL (HeatAmbientDrift.value μ H f hf hfm T),
    Lp.coeFn_add (((innerSL ℝ φ).compLpL 2 μ) (HeatAmbientDrift.value μ H f hf hfm T))
      (∫ t,P (Q t) ∂timeMeasure T),hInt,
    HeatControlConvolution.time_memLp μ H f hf hfm] with ω hQT hQr hR hRp hsum hI hpath
  rw [hQT,hsum]
  simp only [Pi.add_apply]
  rw [hRp,hQr,hR,hI]
  change inner ℝ φ (HeatControlConvolution.value H family f T ω)=
    inner ℝ φ (∫ s,f (s,ω) ∂timeMeasure T)+
      ∫ t,inner ℝ ψ (HeatControlConvolution.value H family f t ω) ∂timeMeasure T
  exact (HeatWeakControlPath.weak_equation hT (fun s => f (s,ω))
    (hf.comp (measurable_id.prodMk measurable_const)) (hpath.integrable (by norm_num)) φ ψ hφ).2

end HeatWeakControlLp
#check @HeatWeakControlLp.weak_equation
#print HeatWeakControlLp.weak_equation
#print axioms HeatWeakControlLp.weak_equation
