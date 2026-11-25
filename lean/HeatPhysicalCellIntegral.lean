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
namespace HeatPhysicalCellIntegral
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
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hT : ∀ n,n ≤ N → t n ≤ H)
    (g : Base) (hgsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → g x=0)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (hpos : t (j-1)<t j)
    (hnext : t (j+1)-t j ≤ t j-t (j-1))
    (I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ H)
    (sol : HeatBackwardModel.Solution F μ H (noise b hb hbound) I W t N g) :

    (∫ ω,∫ s in Ioc (t (j-1)) (t j),
      ‖paperBstar (HeatBackwardModel.path H (noise b hb hbound) W t N g s ω)‖^2 ∂SHE.PredictableL2.timeMeasure H ∂μ) ≤
      ‖g‖^2*(1/2+((t j:ℝ)-(t (j-1):ℝ))/3)*Real.exp (-4/((t j:ℝ)-(t (j-1):ℝ)))*
        (∏ k∈Finset.range (j-1),((t (k+1):ℝ)-(t k:ℝ))⁻¹) := by
  let X := HeatBackwardModel.path H (noise b hb hbound) W t N g
  let f := fun p : ℝ≥0 × Ω => ‖paperBstar (X p.1 p.2)‖^2
  let C := ‖g‖^2*Real.exp (-4/((t j:ℝ)-(t (j-1):ℝ)))*
    (∏ k∈Finset.range (j-1),((t (k+1):ℝ)-(t k:ℝ))⁻¹)
  have hX : StronglyMeasurable (Function.uncurry X) :=
    sol.path_predictable.mono (predictable_le_product F)
  have hfi : Integrable f (energyMeasure μ H) :=
    HeatPathObservation.integrable μ H X sol.path_continuous hX sol.maximum_energy paperBstar
  have hfcell : Integrable f (((SHE.PredictableL2.timeMeasure H).restrict (Ioc (t (j-1)) (t j))).prod μ) :=
    hfi.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hfp : IntegrableOn (fun s => ∫ ω,f (s,ω) ∂μ) (Ioc (t (j-1)) (t j)) (SHE.PredictableL2.timeMeasure H) :=
    hfi.integral_prod_left.integrableOn
  have hwi := (HeatNNObservationPolynomial.integrable H (t (j-1)) (t j)).const_mul C
  have hpoint : ∀ s∈Ioc (t (j-1)) (t j),
      (∫ ω,f (s,ω) ∂μ) ≤ C*HeatNNObservationPolynomial.weight (t (j-1)) (t j) s := by
    intro s hs
    have he := HeatPhysicalCellObservation.expectation_bound F μ H J hlocal W hW hWa b hb hbound hsupp
      t ht N hT g hgsupp j hj hjN hpos hnext s hs.1.le hs.2
    have hpath : (fun ω => f (s,ω))=fun ω => ‖paperBstar (HeatBackwardNodes.cellState family
        family_continuous family_contraction (noise b hb hbound) H W t N g j s ω)‖^2 := by
      funext ω
      dsimp only [f,X,HeatBackwardModel.path]
      rw [HeatBackwardCellRestriction.state_cell family family_continuous family_contraction
        (noise b hb hbound) W t ht N (by omega : 1 ≤ N) g j (Finset.mem_Icc.mpr ⟨hj,hjN⟩) s hs ω]
    rw [hpath]
    convert he using 1 <;> dsimp only [C,HeatNNObservationPolynomial.weight] <;> ring
  calc
    _ = ∫ s in Ioc (t (j-1)) (t j),∫ ω,f (s,ω) ∂μ ∂SHE.PredictableL2.timeMeasure H :=
      (integral_integral_swap hfcell).symm
    _ ≤ ∫ s in Ioc (t (j-1)) (t j),C*HeatNNObservationPolynomial.weight (t (j-1)) (t j) s ∂SHE.PredictableL2.timeMeasure H := by
      apply integral_mono_ae hfp hwi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using hpoint s hs
    _ = _ := by
      rw [integral_const_mul,HeatNNObservationPolynomial.integral hpos (hT j hjN)]
      dsimp only [C]
      ring

end HeatPhysicalCellIntegral
#check @HeatPhysicalCellIntegral.bound
#print axioms HeatPhysicalCellIntegral.bound
