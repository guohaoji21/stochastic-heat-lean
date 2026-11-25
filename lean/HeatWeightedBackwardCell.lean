import HeatBackwardDrift
import HeatHilbertPastMultiplier
import HeatWeightedCellInput

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatWeightedBackwardCell
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal Topology
variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

def input {a t b : ℝ≥0} (hat : a ≤ t) (C : Ω → ℝ)
    (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) (q : E) : Process (E := E) F μ H :=
  HeatWeightedCellInput.constant F μ H t b C (hC.mono (F.mono hat)) hCm (S (b-t) q)

include basis J in
theorem input_integral (hlocal : StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    {a t b : ℝ≥0} (hat : a ≤ t) (htb : t ≤ b) (hbH : b ≤ H)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) (q : E) :
    (I).integral (input F μ H S (b := b) hat C hC hCm q) =ᵐ[μ]
      (fun ω => C ω • ((W b ω-W t ω) • S (b-t) q)) := by
  let U := RotatedCylindricalCoordinates.constant F μ H (S (b-t) q)
  have hv : input F μ H S (b := b) hat C hC hCm q =ᵐ[energyMeasure μ H]
      (fun p => PredictableSteps.step t b C p • U p) := by
    filter_upwards [HeatWeightedCellInput.constant_ae F μ H t b C (hC.mono (F.mono hat)) hCm (S (b-t) q),
      RotatedCylindricalCoordinates.constant_ae F μ H (S (b-t) q)] with p hp hu
    exact hp.trans (by rw [hu])
  have hh := HeatHilbertPastMultiplier.cell F μ H basis J hlocal U
    (input F μ H S (b := b) hat C hC hCm q) t b htb C (hC.mono (F.mono hat)) hv
  have hn := HeatBackwardCell.noise_integral F μ H S basis J W hW htb hbH q
  have hrep : ((I).integral (HeatBackwardCell.noiseInput F μ H S t b q) : Ω → E) =ᵐ[μ]
      (fun ω => (I).integral (StoppedItoInputs.stop F μ H b U) ω -
        (I).integral (StoppedItoInputs.stop F μ H t U) ω) := by
    unfold HeatBackwardCell.noiseInput
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hh,hn,hrep] with ω hh hn hr
  exact hh.trans (congrArg (fun z : E => C ω • z) (hr.symm.trans hn))

include hS hcontr in
theorem state_continuous (W : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => W t ω))
    {a b : ℝ≥0} (hbH : b ≤ H) (C : Ω → ℝ) (q : E) (ω : Ω) :
    Continuous (fun t => C ω • HeatBackwardCell.state H S M W a b q t ω) :=
  (HeatBackwardDrift.state_continuous S hS hcontr M hbH W hc a q ω).const_smul _

include basis J in
theorem mild_equation (hlocal : StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    {a t b : ℝ≥0} (hat : a ≤ t) (htb : t ≤ b) (hbH : b ≤ H)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) (q : E) :
    (fun ω => C ω • HeatBackwardCell.state H S M W a b q t ω) =ᵐ[μ]
      (fun ω => S (b-t) (C ω • ((W b ω-W a ω) • q)) +
        (∫ s in Set.Ioc t b, S (s-t) (M (C ω • S (b-s) q)) ∂timeMeasure H) -
        (I).integral (input F μ H S (b := b) hat C hC hCm q) ω) := by
  filter_upwards [input_integral F μ H S basis J hlocal W hW hat htb hbH C hC hCm q] with ω hω
  rw [hω,map_smul,map_smul]
  have hd : (∫ s in Set.Ioc t b, S (s-t) (M (C ω • S (b-s) q)) ∂timeMeasure H) =
      C ω • HeatBackwardCell.drift H S M t b q := by
    simp only [map_smul,HeatBackwardCell.drift]
    exact integral_smul _ _
  rw [hd]
  unfold HeatBackwardCell.state
  module

end HeatWeightedBackwardCell
#check @HeatWeightedBackwardCell.input_integral
#print axioms HeatWeightedBackwardCell.input_integral
#check @HeatWeightedBackwardCell.state_continuous
#print axioms HeatWeightedBackwardCell.state_continuous
#check @HeatWeightedBackwardCell.mild_equation
#print axioms HeatWeightedBackwardCell.mild_equation
