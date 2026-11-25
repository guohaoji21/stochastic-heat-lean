import HeatRegularizedMildCell
import HeatPartitionPairings
import HeatPartitionEnergy

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatPartitionIdentity
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem identity (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (hlocal : StandardTerminalPastLocality J)
    (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))
    (V Z : ℝ≥0 → Lp E 2 μ) (u v : Process (E := E) F μ H)
    (hVa : ∀ a, a≤H → AEStronglyMeasurable[F a] (V a) μ)
    (hZa : ∀ a, a≤H → AEStronglyMeasurable[F a] (Z a) μ)
    (hy : ∀ a b, a≤b → b≤H → V b=((S (b-a)).compLpL 2 μ) (V a)+
      HeatForwardDrift.value μ H S hS hcontr f hf hfm a b+
      (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u))
    (hz : ∀ a b, a≤b → b≤H → Z a=((S (b-a)).compLpL 2 μ) (Z b)+
      HeatActualCellEnergy.drift F μ H S hS hcontr M a b v-
      (I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v))
    (n : ℕ) :
    inner ℝ (V H) (((S (HeatDualityGrid.width n)).compLpL 2 μ) (Z H))-
      inner ℝ (V 0) (((S (HeatDualityGrid.width n)).compLpL 2 μ) (Z 0))=
      (∫ p,inner ℝ (f p) (HeatSampledAdjoint.raw μ H S Z n p) ∂energyMeasure μ H)-
      (∫ p,inner ℝ (M (v p)) (HeatSampledLp.raw μ H S V n p) ∂energyMeasure μ H)-
      (∑ k∈Finset.Icc 1 (ApproximationCells.index n H),HeatPartitionEnergy.mixed F μ H S hS hcontr M I u v n k)+
      (∫ p,inner ℝ (M (u p)) (S (HeatDualityGrid.width n) (v p)) ∂energyMeasure μ H) := by
  let p := HeatDualityGrid.point H n
  let ε := HeatDualityGrid.width n
  let N := ApproximationCells.index n H
  let φ := fun k => inner ℝ (V (p k)) (((S ε).compLpL 2 μ) (Z (p k)))
  let A := fun k => inner ℝ (HeatForwardDrift.value μ H S hS hcontr f hf hfm (p (k-1)) (p k)) (((S ε).compLpL 2 μ) (Z (p k)))
  let B := fun k => inner ℝ (((S ε).compLpL 2 μ) (V (p (k-1)))) (HeatActualCellEnergy.drift F μ H S hS hcontr M (p (k-1)) (p k) v)
  let R := HeatPartitionEnergy.mixed F μ H S hS hcontr M I u v n
  let Q := fun k => ∫ q,(Set.Ioc (p (k-1)) (p k)).indicator
    (fun s => inner ℝ (M (u (s,q.2))) (S ε (v (s,q.2)))) q.1 ∂energyMeasure μ H
  have hcell (k : ℕ) (hk : k∈Finset.Icc 1 N) : φ k-φ (k-1)=A k-B k-R k+Q k := by
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hab : p (k-1)≤p k := HeatDualityGrid.monotone H n (Nat.sub_le k 1)
    have hbH : p k≤H := min_le_right _ _
    have haH : p (k-1)≤H := min_le_right _ _
    have hε : p k-p (k-1)≤ε := by
      have hh := HeatDualityGrid.size H n (k-1)
      simpa only [Nat.sub_add_cancel hk1] using hh
    exact HeatRegularizedMildCell.identity F μ H S hS hcontr M basis J hsem hsym hlocal hab ε hε
      (V (p (k-1))) (V (p k)) (Z (p (k-1))) (Z (p k))
      (HeatForwardDrift.value μ H S hS hcontr f hf hfm (p (k-1)) (p k)) u v
      (hVa _ haH) (hZa _ haH) (hy _ _ hab hbH) (hz _ _ hab hbH)
  have hh : (∑ k∈Finset.Icc 1 N,(φ k-φ (k-1)))=
      ∑ k∈Finset.Icc 1 N,(A k-B k-R k+Q k) := Finset.sum_congr rfl hcell
  rw [HeatTimePartition.telescopes φ N] at hh
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hh
  dsimp only [φ,p,N,ε,A,B,Q] at hh
  rw [HeatDualityGrid.last,HeatDualityGrid.first,
    HeatPartitionPairings.control_sum μ H S hS hcontr hsem hsym f hf hfm Z n,
    HeatPartitionPairings.drift_sum F μ H S hS hcontr M hsem hsym V v n,
    HeatPartitionPairings.noise_sum F μ H S M u v n] at hh
  exact hh

end HeatPartitionIdentity
#check @HeatPartitionIdentity.identity
#print HeatPartitionIdentity.identity
#print axioms HeatPartitionIdentity.identity
