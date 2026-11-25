import HeatWeakControlLp
import HeatWeakUncontrolled

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatWeakControlled
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
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem weak_equation (g : Base) (u : Process (E := Base) F μ H)
    (f : ℝ≥0 × Ω → Base) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (Q : ℝ≥0 → Lp Base 2 μ) (hQc : Continuous Q)
    (hQr : ∀ t, Q t=ᵐ[μ] HeatControlConvolution.value H family f t)
    {T : ℝ≥0} (hT : T≤H)
    (hj : Integrable (fun p : ℝ≥0 × Ω => HeatControlConvolution.value H family f p.1 p.2) (energyMeasure μ T))
    (φ ψ : Base) (hφ : weakLaplacian φ ψ) :
    let V := fun t => HeatMildSolution.value F μ H family family_continuous family_contraction M (I) g u t+Q t
    ((innerSL ℝ φ).compLpL 2 μ) (V T)=Lp.const 2 μ (inner ℝ φ g)+
      ((innerSL ℝ φ).compLpL 2 μ) (HeatAmbientDrift.value μ H f hf hfm T)+
      (∫ t,((innerSL ℝ ψ).compLpL 2 μ) (V t) ∂timeMeasure T)+
      ((innerSL ℝ φ).compLpL 2 μ) ((I).integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M u))) := by
  let V₀ := HeatMildSolution.value F μ H family family_continuous family_contraction M (I) g u
  let P := (innerSL ℝ ψ).compLpL 2 μ
  have hi₀ : Integrable (fun t => P (V₀ t)) (timeMeasure T) :=
    HeatCompactTimeIntegrability.of_continuous _ (P.continuous.comp
      (HeatMildSolution.value_continuous F μ H family family_continuous family_contraction M (I) g u)) T
  have hiQ : Integrable (fun t => P (Q t)) (timeMeasure T) :=
    HeatCompactTimeIntegrability.of_continuous _ (P.continuous.comp hQc) T
  have hsum : (∫ t,P (V₀ t+Q t) ∂timeMeasure T)=
      (∫ t,P (V₀ t) ∂timeMeasure T)+(∫ t,P (Q t) ∂timeMeasure T) := by
    simp_rw [map_add]
    exact integral_add hi₀ hiQ
  have h₀ := HeatWeakUncontrolled.weak_equation F μ H M basis J g u φ ψ hφ T
  have hQ := HeatWeakControlLp.weak_equation μ H f hf hfm Q hQc hQr hT hj φ ψ hφ
  change ((innerSL ℝ φ).compLpL 2 μ) (V₀ T+Q T)=_
  rw [map_add,h₀,hQ]
  change _=Lp.const 2 μ (inner ℝ φ g)+((innerSL ℝ φ).compLpL 2 μ) (HeatAmbientDrift.value μ H f hf hfm T)+
    (∫ t,P (V₀ t+Q t) ∂timeMeasure T)+_
  rw [hsum]
  abel

end HeatWeakControlled
#check @HeatWeakControlled.weak_equation
#print HeatWeakControlled.weak_equation
#print axioms HeatWeakControlled.weak_equation
