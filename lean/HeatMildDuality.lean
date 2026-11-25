import HeatPartitionIdentity
import HeatDualityLimits
import HeatLiftedAlgebra

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatMildDuality
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem duality (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (hM : ‖M‖≤1) (hMsym : ∀ x y, inner ℝ (M x) y=inner ℝ x (M y))
    (hlocal : StandardTerminalPastLocality J)
    (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (V Z : ℝ≥0 → Lp E 2 μ) (u v : Process (E := E) F μ H)
    (hV : Continuous V) (hVu : ∀ᵐ s ∂timeMeasure H, (fun ω => u (s,ω))=ᵐ[μ] V s)
    (C : ℝ) (hC : ∀ s, s≤H → ‖V s‖≤C)
    (X : ℝ≥0 → Ω → E) (hXc : ∀ ω, Continuous (fun t => X t ω)) (hXm : ∀ t, Measurable (X t))
    (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0≤D ω) (hB : ∀ t, t≤H → ∀ ω, ‖X t ω‖≤D ω)
    (hZrep : ∀ t, t≤H → Z t=ᵐ[μ] X t)
    (hVa : ∀ a, a≤H → AEStronglyMeasurable[F a] (V a) μ)
    (hZa : ∀ a, a≤H → AEStronglyMeasurable[F a] (Z a) μ)
    (hy : ∀ a b, a≤b → b≤H → V b=((S (b-a)).compLpL 2 μ) (V a)+
      HeatForwardDrift.value μ H S hS hcontr f hf hfm a b+
      (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u))
    (hz : ∀ a b, a≤b → b≤H → Z a=((S (b-a)).compLpL 2 μ) (Z b)+
      HeatActualCellEnergy.drift F μ H S hS hcontr M a b v-
      (I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v)) :
    inner ℝ (V H) (Z H)=inner ℝ (V 0) (Z 0)+
      (∫ p,inner ℝ (f p) (X p.1 p.2) ∂energyMeasure μ H) := by
  have hcontrol := HeatDualityLimits.control μ H S hS hcontr hzero f hfm X hXc hXm D hD hD0 hB
  have hcontrol' : Tendsto (fun n => ∫ p,inner ℝ (f p) (HeatSampledAdjoint.raw μ H S Z n p) ∂energyMeasure μ H)
      atTop (𝓝 (∫ p,inner ℝ (f p) (X p.1 p.2) ∂energyMeasure μ H)) := by
    apply hcontrol.congr'
    apply Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [HeatSampledAdjoint.raw_ae μ H S Z X hZrep n] with p hp
    rw [hp]
  have hdrift := HeatDualityLimits.drift F μ H S hS hcontr hzero M V hV u v hVu C hC
  have hnoise := HeatDualityLimits.noise F μ H S hS hcontr hzero M u v
  have hmixed := HeatPartitionEnergy.mixed_tends_zero F μ H S hS hcontr M I hM u v
  have hdn : (∫ p,inner ℝ (M (v p)) (u p) ∂energyMeasure μ H)=
      (∫ p,inner ℝ (M (u p)) (v p) ∂energyMeasure μ H) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => (hMsym (v p) (u p)).trans (real_inner_comm _ _))
  have hr := ((hcontrol'.sub hdrift).sub hmixed).add hnoise
  rw [hdn,sub_zero,sub_add_cancel] at hr
  have hregular (Y : Lp E 2 μ) : Tendsto (fun n => ((S (HeatDualityGrid.width n)).compLpL 2 μ) Y) atTop (𝓝 Y) := by
    have hh := (HeatLiftedSemigroup.continuous μ S hS hcontr Y).continuousAt.tendsto.comp HeatDualityGrid.width_tendsto
    have hz : HeatLiftedSemigroup.family μ S 0 Y=Y := by
      rw [HeatLiftedAlgebra.zero μ S hzero]
      rfl
    rw [hz] at hh
    exact hh
  have hVH : Tendsto (fun _ : ℕ => V H) atTop (𝓝 (V H)) := tendsto_const_nhds
  have hV0 : Tendsto (fun _ : ℕ => V 0) atTop (𝓝 (V 0)) := tendsto_const_nhds
  have hl : Tendsto (fun n => inner ℝ (V H) (((S (HeatDualityGrid.width n)).compLpL 2 μ) (Z H))-
      inner ℝ (V 0) (((S (HeatDualityGrid.width n)).compLpL 2 μ) (Z 0)))
      atTop (𝓝 (inner ℝ (V H) (Z H)-inner ℝ (V 0) (Z 0))) :=
    (hVH.inner (hregular (Z H))).sub (hV0.inner (hregular (Z 0)))
  have hright := hr.congr' (Eventually.of_forall (fun n =>
    (HeatPartitionIdentity.identity F μ H S hS hcontr M basis J hsem hsym hlocal f hf hfm V Z u v hVa hZa hy hz n).symm))
  have he := tendsto_nhds_unique hl hright
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

end HeatMildDuality
#check @HeatMildDuality.duality
#print HeatMildDuality.duality
#print axioms HeatMildDuality.duality
