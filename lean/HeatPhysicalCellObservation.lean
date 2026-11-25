import HeatBackwardNodes
import HeatObservedBackwardCell
import HeatBrownianProductMoments
import HeatChainSeparation

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatPhysicalCellObservation
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

theorem expectation_bound (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0,s ≤ H → (J.integral (StoppedItoInputs.stop F μ H s R) : Ω → ℝ)=ᵐ[μ] W s)
    (hWa : ∀ s,StronglyMeasurable[F s] (W s))
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → b x=0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hT : ∀ n,n ≤ N → t n ≤ H)
    (g : Base) (hgsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → g x=0)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (hpos : t (j-1)<t j)
    (hnext : t (j+1)-t j ≤ t j-t (j-1)) (s : ℝ≥0)
    (has : t (j-1) ≤ s) (hsc : s ≤ t j) :
    (∫ ω,‖paperBstar (HeatBackwardNodes.cellState family family_continuous family_contraction
      (noise b hb hbound) H W t N g j s ω)‖^2 ∂μ) ≤
      ‖g‖^2*Real.exp (-4/((t j:ℝ)-(t (j-1):ℝ)))*
        (∏ k∈Finset.range (j-1),((t (k+1):ℝ)-(t k:ℝ))⁻¹)*
          (((s:ℝ)-(t (j-1):ℝ))+((t j:ℝ)-(s:ℝ))^2)/((t j:ℝ)-(t (j-1):ℝ))^2 := by
  let h : ℕ → ℝ≥0 := fun k => t k-t (k-1)
  let q := HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound) h N g j
  let ζ := HeatBrownianProducts.products W t (j-1)
  let C := Real.exp (-4/(2*(h j:ℝ)))*‖g‖
  have hp := HeatBrownianProducts.products_properties F μ H J hlocal W hW hWa t ht N hT (j-1) (by omega)
  have hP := HeatBrownianProductMoments.expectation F μ H J hlocal W hW hWa t ht N hT (j-1) (by omega)
  have hh : 0<(h j:ℝ) := by dsimp [h];rw [NNReal.coe_sub hpos.le];exact sub_pos.mpr (by exact_mod_cast hpos)
  have hr : t j-s ≤ h j := tsub_le_tsub_left has (t j)
  have hA : ‖paperBstar (family (t j-s) q)‖ ≤ C :=
    HeatChainSeparation.heat_state_bound b hb hbound hsupp h N g hgsupp j hjN (t j-s) hr hh
      (by simpa only [h,show j+1-1=j by omega] using hnext)
  have hB : ‖paperBstar (HeatPaperCovariance.K b hb hbound (t j-s) q)‖ ≤ C :=
    HeatChainSeparation.covariance_state_bound b hb hbound hsupp h N g j (t j-s) hr hh
  have he := HeatObservedBackwardCell.expectation F μ H J hlocal W hW family family_continuous
    family_contraction (noise b hb hbound) paperBstar has hsc (hT j hjN) ζ hp.1 hp.2 q
  change (∫ ω,‖paperBstar (HeatBackwardNodes.cellState family family_continuous family_contraction
    (noise b hb hbound) H W t N g j s ω)‖^2 ∂μ)=_ at he
  have hZ : 0 ≤ ∫ ω,ζ ω^2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have he0 : 0 ≤ (s:ℝ)-(t (j-1):ℝ) := sub_nonneg.mpr (by exact_mod_cast has)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hA2 : ‖paperBstar (family (t j-s) q)‖^2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hB2 : ‖paperBstar (HeatPaperCovariance.K b hb hbound (t j-s) q)‖^2 ≤ C^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hC2 : C^2=Real.exp (-4/(h j:ℝ))*‖g‖^2 := by
    dsimp only [C]
    rw [mul_pow,pow_two (Real.exp _),←Real.exp_add]
    congr 1
    congr 1
    field_simp
    <;> ring
  calc
    _ = _ := he
    _ ≤ (((t j:ℝ)-(t (j-1):ℝ))⁻¹)^2*(∫ ω,ζ ω^2 ∂μ)*
        (((s:ℝ)-(t (j-1):ℝ))*C^2+((t j-s:ℝ≥0):ℝ)^2*C^2) := by
      change _ ≤ _
      gcongr <;> assumption
    _ = _ := by
      rw [hC2]
      change _*(∫ ω,HeatBrownianProducts.products W t (j-1) ω^2 ∂μ)*_= _
      rw [hP]
      dsimp only [h]
      rw [NNReal.coe_sub hpos.le,NNReal.coe_sub hsc]
      simp only [div_eq_mul_inv,inv_pow]
      ring

end HeatPhysicalCellObservation
#check @HeatPhysicalCellObservation.expectation_bound
#print axioms HeatPhysicalCellObservation.expectation_bound
