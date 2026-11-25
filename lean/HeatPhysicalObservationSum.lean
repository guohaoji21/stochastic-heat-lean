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
namespace HeatPhysicalObservationSum
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
    (ht0 : t 0=0) (hTN : t N=H) (hN : 1 ≤ N)
    (hstep : ∀ n,n<N → t n<t (n+1))
    (hnext : ∀ j,1 ≤ j → j ≤ N → t (j+1)-t j ≤ t j-t (j-1))
    (hlength : ∀ j,1 ≤ j → j ≤ N → t j-t (j-1) ≤ 1)
    (I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ H)
    (sol : HeatBackwardModel.Solution F μ H (noise b hb hbound) I W t N g) :


    (∫ p : ℝ≥0 × Ω,‖paperBstar (HeatBackwardModel.path H (noise b hb hbound) W t N g p.1 p.2)‖^2
      ∂energyMeasure μ H) ≤
      ‖g‖^2*(∑ n∈Finset.range N,Real.exp (-4/((t (n+1)-t n:ℝ≥0):ℝ))*
        (∏ k∈Finset.range n,(((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) := by
  let X := HeatBackwardModel.path H (noise b hb hbound) W t N g
  let f := fun p : ℝ≥0 × Ω => ‖paperBstar (X p.1 p.2)‖^2
  have hX : StronglyMeasurable (Function.uncurry X) :=
    sol.path_predictable.mono (predictable_le_product F)
  have hfi : Integrable f (energyMeasure μ H) :=
    HeatPathObservation.integrable μ H X sol.path_continuous hX sol.maximum_energy paperBstar
  have hfp := hfi.integral_prod_left
  have hh (k : ℕ) : ((t (k+1)-t k:ℝ≥0):ℝ)=(t (k+1):ℝ)-(t k:ℝ) :=
    NNReal.coe_sub (ht (Nat.le_succ k))
  have hcell (n : ℕ) (hn : n∈Finset.range N) :
      (∫ s in Ioc (t n) (t (n+1)),∫ ω,f (s,ω) ∂μ ∂SHE.PredictableL2.timeMeasure H) ≤
        ‖g‖^2*(Real.exp (-4/((t (n+1)-t n:ℝ≥0):ℝ))*
          (∏ k∈Finset.range n,(((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) := by
    have hnlt : n<N := Finset.mem_range.mp hn
    have hfcell : Integrable f (((SHE.PredictableL2.timeMeasure H).restrict (Ioc (t n) (t (n+1)))).prod μ) :=
      hfi.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
    have he := HeatPhysicalCellIntegral.bound F μ H J hlocal W hW hWa b hb hbound hsupp t ht N hT
      g hgsupp (n+1) (by omega) (by omega) (by simpa only [Nat.add_sub_cancel] using hstep n hnlt)
      (hnext (n+1) (by omega) (by omega)) I sol
    simp only [Nat.add_sub_cancel] at he
    have hpoly : (1/2:ℝ)+((t (n+1):ℝ)-(t n:ℝ))/3 ≤ 1 := by
      have hc := hlength (n+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hc
      have hcr : ((t (n+1)-t n:ℝ≥0):ℝ) ≤ 1 := by exact_mod_cast hc
      rw [hh n] at hcr
      linarith
    have hprod0 : 0 ≤ ∏ k∈Finset.range n,((t (k+1):ℝ)-(t k:ℝ))⁻¹ := by
      apply Finset.prod_nonneg
      intro k _
      exact inv_nonneg.mpr (sub_nonneg.mpr (by exact_mod_cast ht (Nat.le_succ k)))
    calc
      _ = ∫ ω,∫ s in Ioc (t n) (t (n+1)),f (s,ω) ∂SHE.PredictableL2.timeMeasure H ∂μ :=
        integral_integral_swap hfcell
      _ ≤ _ := he
      _ ≤ ‖g‖^2*1*Real.exp (-4/((t (n+1):ℝ)-(t n:ℝ)))*
          (∏ k∈Finset.range n,((t (k+1):ℝ)-(t k:ℝ))⁻¹) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (sq_nonneg ‖g‖)) (Real.exp_pos _).le) hprod0
      _ = _ := by simp_rw [hh];ring
  calc
    _ = ∫ s,∫ ω,f (s,ω) ∂μ ∂SHE.PredictableL2.timeMeasure H := integral_prod _ hfi
    _ = ∑ n∈Finset.range N,∫ s in Ioc (t n) (t (n+1)),∫ ω,f (s,ω) ∂μ ∂SHE.PredictableL2.timeMeasure H :=
      (HeatPartitionIntegral.whole _ hfp t ht ht0 N hTN).symm
    _ ≤ ∑ n∈Finset.range N,‖g‖^2*(Real.exp (-4/((t (n+1)-t n:ℝ≥0):ℝ))*
        (∏ k∈Finset.range n,(((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) := Finset.sum_le_sum hcell
    _ = _ := (Finset.mul_sum ..).symm

end HeatPhysicalObservationSum
#check @HeatPhysicalObservationSum.bound
#print axioms HeatPhysicalObservationSum.bound
