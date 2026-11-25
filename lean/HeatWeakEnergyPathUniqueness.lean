import HeatWeakEnergyEstimate
import HeatWeakEnergyDifference
import HeatStoppedProcessBound
import HeatStoppedSliceEnergy
import HeatResolventGradient
import HeatResolventLpConvergence
import HeatZeroGronwall
import HeatWeakEnergyIto
import HeatItoNormEnergyAt
import SHE.StoppedDampingClock

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatWeakEnergyPathUniqueness
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatDirichletResolvent HeatWeakEnergyEquation
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
variable (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (s₁ s₂ : HeatWeakEnergyModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g)


theorem path_same (hlocal : StandardTerminalPastLocality J) :
    ∀ᵐ ω ∂μ,∀ a,a ≤ H → s₁.path a ω=s₂.path a ω := by
  have he (a : Set.Iic H) : ∀ᵐ ω ∂μ,edist (s₁.path a ω) (s₂.path a ω)=0 := by
    have h₁ := s₁.path_version a a.property
    rw [HeatWeakEnergyEstimate.value_same F μ H M basis J U hU hE g s₁ s₂ hlocal a a.property] at h₁
    filter_upwards [h₁,s₂.path_version a a.property] with ω h₁ h₂
    rw [h₁,h₂,edist_self]
  have hi := ProbabilityTheory.indistinguishable_of_edist_modification
    (Eventually.of_forall (fun ω => (s₁.path_continuous ω).comp continuous_subtype_val))
    (Eventually.of_forall (fun ω => (s₂.path_continuous ω).comp continuous_subtype_val)) he
  filter_upwards [hi] with ω hω a ha
  exact edist_eq_zero.mp (hω ⟨a,ha⟩)

end HeatWeakEnergyPathUniqueness
#check @HeatWeakEnergyPathUniqueness.path_same
#print axioms HeatWeakEnergyPathUniqueness.path_same
