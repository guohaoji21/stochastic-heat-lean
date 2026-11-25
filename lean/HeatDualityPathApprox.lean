import HeatDualityEndpoints
import HeatPredictableSemigroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatDualityPathApprox
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖)

def raw (X : ℝ≥0 → Ω → E) (n : ℕ) (p : ℝ≥0 × Ω) : E :=
  S (HeatDualityGrid.width n+(HeatDualityEndpoints.right H n p.1-p.1))
    (X (HeatDualityEndpoints.right H n p.1) p.2)

include hS hcontr in
theorem approximation (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (X : ℝ≥0 → Ω → E) (hc : ∀ ω, Continuous (fun t => X t ω)) (hm : ∀ t, Measurable (X t))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0≤D ω)
    (hB : ∀ t, t≤H → ∀ ω, ‖X t ω‖≤D ω) :
    Tendsto (fun n => ∫ p,‖raw H S X n p-X p.1 p.2‖^2 ∂energyMeasure μ H) atTop (𝓝 0) := by
  have hX : Measurable (Function.uncurry X) := measurable_uncurry_of_continuous_of_measurable hc hm
  have hraw (n : ℕ) : Measurable (raw H S X n) := by
    have hr : Measurable (fun p : ℝ≥0 × Ω => HeatDualityEndpoints.right H n p.1) :=
      (HeatDualityEndpoints.measurable H n).2.comp measurable_fst
    have ht : Measurable (fun p : ℝ≥0 × Ω => HeatDualityGrid.width n+(HeatDualityEndpoints.right H n p.1-p.1)) :=
      measurable_const.add (hr.sub measurable_fst)
    exact (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
      (ht.prodMk (hX.comp (hr.prodMk measurable_snd)))
  have hdom : Integrable (fun p : ℝ≥0 × Ω => 4*(D p.2)^2) (energyMeasure μ H) :=
    ((hD.comp_snd (timeMeasure H)).integrable_sq).const_mul 4
  have hbound (n : ℕ) : ∀ᵐ p ∂energyMeasure μ H, ‖‖raw H S X n p-X p.1 p.2‖^2‖≤4*(D p.2)^2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    have hright : HeatDualityEndpoints.right H n p.1≤H := min_le_right _ _
    have hn : ‖raw H S X n p-X p.1 p.2‖≤2*D p.2 :=
      (norm_sub_le _ _).trans (by
        have hh := (hcontr (HeatDualityGrid.width n+(HeatDualityEndpoints.right H n p.1-p.1))
          (X (HeatDualityEndpoints.right H n p.1) p.2)).trans (hB _ hright p.2)
        change ‖raw H S X n p‖≤D p.2 at hh
        linarith [hB p.1 hp.2 p.2])
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by ring)
  have hlim : ∀ᵐ p ∂energyMeasure μ H, Tendsto (fun n => ‖raw H S X n p-X p.1 p.2‖^2) atTop (𝓝 0) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    have hr := HeatDualityEndpoints.right_tendsto H hp.1 hp.2
    have hconst : Tendsto (fun _ : ℕ => p.1) atTop (𝓝 p.1) := tendsto_const_nhds
    have ht : Tendsto (fun n => HeatDualityGrid.width n+(HeatDualityEndpoints.right H n p.1-p.1)) atTop (𝓝 0) := by
      simpa only [tsub_self,add_zero] using HeatDualityGrid.width_tendsto.add (hr.sub hconst)
    have hv := (HeatPredictableSemigroup.continuous_action S hS hcontr).tendsto (0,X p.1 p.2) |>.comp
      (ht.prodMk_nhds ((hc p.2).continuousAt.tendsto.comp hr))
    have he := (hv.sub_const (X p.1 p.2)).norm.pow 2
    simpa only [raw,Function.comp_apply,hzero,ContinuousLinearMap.id_apply,sub_self,norm_zero,zero_pow (by omega : 2≠0)] using he
  have hmerr (n : ℕ) : AEStronglyMeasurable
      (fun p : ℝ≥0 × Ω => ‖raw H S X n p-X p.1 p.2‖^2) (energyMeasure μ H) := by
    exact ((hraw n).sub hX).stronglyMeasurable.norm.pow 2 |>.aestronglyMeasurable
  have he := tendsto_integral_of_dominated_convergence (fun p : ℝ≥0 × Ω => 4*(D p.2)^2)
    hmerr hdom hbound hlim
  simpa only [Pi.pow_apply,Pi.sub_apply,Function.uncurry,Pi.zero_apply,integral_zero] using he

end HeatDualityPathApprox
#check @HeatDualityPathApprox.approximation
#print HeatDualityPathApprox.approximation
#print axioms HeatDualityPathApprox.approximation
