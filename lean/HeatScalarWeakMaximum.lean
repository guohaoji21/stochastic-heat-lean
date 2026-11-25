import HeatScalarControlBound
import HeatContinuousAEBound
import HeatContinuousTimeIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatScalarWeakMaximum
open MeasureTheory Filter Set SHE.PredictableL2
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem bound (X N : ℝ≥0 → Ω → ℝ) (D : Ω → ℝ) (x0 c : ℝ) (hc : 0≤c)
    (hX : ∀ ω, Continuous (X · ω)) (hD : ∀ ω,0≤D ω)
    (hN : ∀ t, t≤H → ∀ ω, |N t ω|≤D ω)
    (f : ℝ≥0 × Ω → ℝ) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (heq : ∀ t, t≤H → ∀ᵐ ω ∂μ,
      X t ω+c*(∫ s,X s ω ∂timeMeasure t)=x0+(∫ s,f (s,ω) ∂timeMeasure t)+N t ω) :
    ∀ᵐ ω ∂μ, ∀ t, t≤H → |X t ω|≤2*(|x0|+HeatScalarControlBound.bound H f ω+D ω) := by
  let A (t : ℝ≥0) (ω : Ω) := X t ω+c*(∫ s,X s ω ∂timeMeasure t)
  let B (ω : Ω) := |x0|+HeatScalarControlBound.bound H f ω+D ω
  have hAc (ω : Ω) : Continuous (A · ω) :=
    (hX ω).add ((HeatContinuousTimeIntegral.continuous _ (hX ω)).const_mul c)
  have hbound (t : Iic H) : ∀ᵐ ω ∂μ, |A t ω|≤B ω := by
    filter_upwards [heq t t.property,HeatScalarControlBound.integral_bound μ H f hf hfm t t.property] with ω he hfω
    change |X t ω+c*(∫ s,X s ω ∂timeMeasure t)|≤B ω
    rw [he]
    have ha := abs_add_le (x0+(∫ s,f (s,ω) ∂timeMeasure t)) (N t ω)
    have hb := abs_add_le x0 (∫ s,f (s,ω) ∂timeMeasure t)
    dsimp [B]
    linarith [hN t t.property ω]
  have hall := HeatContinuousAEBound.bound μ (fun t : Iic H => fun ω => |A t ω|) B
    (Eventually.of_forall (fun ω => (hAc ω).abs.comp continuous_subtype_val)) hbound
  filter_upwards [hall] with ω hω
  have hB : 0≤B ω := by
    dsimp [B]
    exact add_nonneg (add_nonneg (abs_nonneg _) (HeatScalarControlBound.nonnegative H f ω)) (hD ω)
  apply HeatScalarDampingNNReal.bound (x := fun t => X t ω) (F := fun t => A t ω) hc hB (hX ω)
    (fun t ht => hω ⟨t,ht⟩)
  intro t ht
  rfl

end HeatScalarWeakMaximum
#check @HeatScalarWeakMaximum.bound
#print HeatScalarWeakMaximum.bound
#print axioms HeatScalarWeakMaximum.bound
