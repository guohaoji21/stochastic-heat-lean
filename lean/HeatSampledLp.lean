import HeatJointL2
import HeatDualityMeanSquare

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatSampledLp
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

def raw (V : ℝ≥0 → Lp E 2 μ) (n : ℕ) (p : ℝ≥0 × Ω) : E :=
  S (HeatDualityGrid.width n+(p.1-HeatDualityEndpoints.left H n p.1))
    (V (HeatDualityEndpoints.left H n p.1) p.2)

theorem raw_ae (V : ℝ≥0 → Lp E 2 μ) (n : ℕ) (s : ℝ≥0) :
    (fun ω => raw μ H S V n (s,ω))=ᵐ[μ]
      HeatLiftedSemigroup.family μ S (HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s))
        (V (HeatDualityEndpoints.left H n s)) :=
  by
    filter_upwards [((S (HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s))).coeFn_compLpL
      (V (HeatDualityEndpoints.left H n s)))] with ω hω
    exact hω.symm

include hS hcontr in
theorem measurable (V : ℝ≥0 → Lp E 2 μ) (n : ℕ) : Measurable (raw μ H S V n) := by
  have hi : Measurable (fun p : ℝ≥0 × Ω => ApproximationCells.index n p.1) :=
    (Nat.measurable_ceil.comp (measurable_coe_nnreal_real.div_const (ApproximationClock.delta n))).comp measurable_fst
  have hcoef : Measurable (fun p : ℕ × Ω => V (HeatDualityGrid.point H n (p.1-1)) p.2) :=
    measurable_uncurry_of_continuous_of_measurable (fun _ => continuous_of_discreteTopology)
      (fun k => (Lp.stronglyMeasurable (V (HeatDualityGrid.point H n (k-1)))).measurable)
  have hl := (HeatDualityEndpoints.measurable H n).1.comp (measurable_fst : Measurable (Prod.fst : ℝ≥0 × Ω → ℝ≥0))
  have ht : Measurable (fun p : ℝ≥0 × Ω => HeatDualityGrid.width n+(p.1-HeatDualityEndpoints.left H n p.1)) :=
    measurable_const.add (measurable_fst.sub hl)
  exact (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
    (ht.prodMk (hcoef.comp (hi.prodMk measurable_snd)))

include hS hcontr in
theorem square_integrable (V : ℝ≥0 → Lp E 2 μ) (C : ℝ)
    (hC : ∀ s, s≤H → ‖V s‖≤C) (n : ℕ) :
    MemLp (raw μ H S V n) 2 (energyMeasure μ H) := by
  have hC0 : 0≤C := (norm_nonneg _).trans (hC 0 zero_le)
  have hfm (s : ℝ≥0) : MemLp (fun ω => raw μ H S V n (s,ω)) 2 μ :=
    MemLp.ae_eq (raw_ae μ H S V n s).symm (Lp.memLp _)
  apply HeatJointL2.of_fibre_bound μ H _ (measurable μ H S hS hcontr V n) hfm (C^2)
  intro s
  let R := HeatLiftedSemigroup.family μ S (HeatDualityGrid.width n+(s-HeatDualityEndpoints.left H n s))
    (V (HeatDualityEndpoints.left H n s))
  have hnorm : (∫ ω,‖raw μ H S V n (s,ω)‖^2 ∂μ)=‖R‖^2 := by
    rw [realLp_norm_sq]
    exact integral_congr_ae ((raw_ae μ H S V n s).fun_comp (fun z : E => ‖z‖^2))
  rw [hnorm]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((HeatLiftedSemigroup.contraction μ S hcontr _ _).trans (hC _ (min_le_right _ _))) 2

end HeatSampledLp
#check @HeatSampledLp.raw_ae
#print axioms HeatSampledLp.raw_ae
#check @HeatSampledLp.measurable
#print axioms HeatSampledLp.measurable
#check @HeatSampledLp.square_integrable
#print HeatSampledLp.square_integrable
#print axioms HeatSampledLp.square_integrable
