import HeatGridDecay
import HeatPhysicalObservationSum
import HeatPhysicalCellIntegral
import HeatPartitionIntegral
import HeatPhysicalCellObservation
import HeatNNObservationPolynomial
import HeatPathObservation
import HeatBackwardModel
import HeatBackwardCellRestriction
import HeatBackwardNodes
import HeatObservedBackwardCell
import HeatBrownianProductMoments
import HeatChainSeparation

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatLogObservation
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal BigOperators
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem bound (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0,s ≤ H → (J.integral (StoppedItoInputs.stop F μ H s R) : Ω → ℝ)=ᵐ[μ] W s)
    (hWa : ∀ s,StronglyMeasurable[F s] (W s))
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → b x=0)
    (L : ℝ) (hL : 1 ≤ L) (N : ℕ) (hN : 1 ≤ N)
    (hbefore : HeatClippedPartition.raw (HeatLogPartition.lengths L hL) (N-1)<H)
    (hend : H ≤ HeatClippedPartition.raw (HeatLogPartition.lengths L hL) N)
    (g : Base) (hgsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → g x=0)
    (I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ H)
    (sol : HeatBackwardModel.Solution F μ H (noise b hb hbound) I W (HeatClippedPartition.nodes (HeatLogPartition.lengths L hL) H) N g) :



    (∫ p : ℝ≥0 × Ω,‖paperBstar (HeatBackwardModel.path H (noise b hb hbound) W
      (HeatClippedPartition.nodes (HeatLogPartition.lengths L hL) H) N g p.1 p.2)‖^2
        ∂energyMeasure μ H) ≤ 2*‖g‖^2*Real.exp (-4*L) := by
  let d := HeatLogPartition.lengths L hL
  let t := HeatClippedPartition.nodes d H
  have hprops := HeatClippedPartition.nodes_properties d H (HeatLogPartition.positive L hL) hN hbefore hend
  have hnext : ∀ j,1 ≤ j → j ≤ N → t (j+1)-t j ≤ t j-t (j-1) := by
    intro j hj _
    exact HeatClippedPartition.lengths_antitone d H (HeatLogPartition.antitone L hL) hN hbefore hend hj
  have hlength : ∀ j,1 ≤ j → j ≤ N → t j-t (j-1) ≤ 1 := by
    intro j hj hjN
    exact (HeatClippedPartition.length_bound d H hN hbefore hend hj hjN).trans
      (HeatLogPartition.le_one L hL (j-1))
  have he := HeatPhysicalObservationSum.bound F μ H J hlocal W hW hWa b hb hbound hsupp t
    (HeatClippedPartition.nodes_mono d H) N (fun n _ => hprops.2.2.2 n) g hgsupp hprops.1 hprops.2.1
    hN hprops.2.2.1 hnext hlength I sol
  have hs := HeatGridDecay.sum_bound L hL H hN hbefore hend
  exact he.trans ((mul_le_mul_of_nonneg_left hs (sq_nonneg ‖g‖)).trans_eq (by ring))

end HeatLogObservation
#check @HeatLogObservation.bound
#print axioms HeatLogObservation.bound
