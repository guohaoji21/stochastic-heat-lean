import HeatDualityPathApprox

set_option autoImplicit false
noncomputable section
namespace HeatSampledAdjoint
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E)

def raw (V : ℝ≥0 → Lp E 2 μ) (n : ℕ) (p : ℝ≥0 × Ω) : E :=
  S (HeatDualityGrid.width n+(HeatDualityEndpoints.right H n p.1-p.1))
    (V (HeatDualityEndpoints.right H n p.1) p.2)

theorem raw_ae (V : ℝ≥0 → Lp E 2 μ) (X : ℝ≥0 → Ω → E)
    (hrep : ∀ t, t≤H → V t=ᵐ[μ] X t) (n : ℕ) :
    raw μ H S V n=ᵐ[energyMeasure μ H] HeatDualityPathApprox.raw H S X n := by
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ,
      V (HeatDualityGrid.point H n k) ω=X (HeatDualityGrid.point H n k) ω :=
    ae_all_iff.mpr (fun k => hrep _ (min_le_right _ _))
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hall] with p hp
  exact congrArg (fun z => S (HeatDualityGrid.width n+(HeatDualityEndpoints.right H n p.1-p.1)) z)
    (hp (ApproximationCells.index n p.1))

end HeatSampledAdjoint
#check @HeatSampledAdjoint.raw_ae
#print HeatSampledAdjoint.raw_ae
#print axioms HeatSampledAdjoint.raw_ae
