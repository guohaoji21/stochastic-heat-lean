import HeatTerminalNaturality
import SHEStochastic.UnboundedPastMultiplier

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatHilbertPastMultiplier
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

def scalarInput (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) : Process (E := Space Unit ℝ) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HeatUnitHilbertLp.lpEquiv ν ((L.compLpL 2 ν) u)

theorem scalarInput_ae (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) :
    scalarInput F μ H L u =ᵐ[energyMeasure μ H] (fun p => HeatUnitHilbertColumns.columnEquiv (L (u p))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have h1 := ae_eq_of_ae_eq_trim (HeatUnitHilbertLp.lpEquiv_ae ν ((L.compLpL 2 ν) u))
  have h2 := ae_eq_of_ae_eq_trim (L.coeFn_compLpL u)
  filter_upwards [h1,h2] with p h1 h2
  change HeatUnitHilbertLp.lpEquiv ν ((L.compLpL 2 ν) u) p = _
  rw [h1,h2]

theorem scalarInput_stop (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) (t : ℝ≥0) :
    scalarInput F μ H L (StoppedItoInputs.stop F μ H t u) =
      StoppedItoInputs.stop F μ H t (scalarInput F μ H L u) := by
  apply SHE.PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [scalarInput_ae F μ H L (StoppedItoInputs.stop F μ H t u),
    scalarInput_ae F μ H L u,StoppedItoInputs.stop_ae F μ H t u,
    StoppedItoInputs.stop_ae F μ H t (scalarInput F μ H L u)] with p h1 h2 h3 h4
  rw [h1,h4,h3]
  by_cases hp : p ∈ StoppedItoInputs.before (t:ℝ)
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,h2]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,map_zero,map_zero]

theorem cell (hlocal : StandardTerminalPastLocality J) (u v : Process (E := E) F μ H)
    (s t : ℝ≥0) (hst : s ≤ t) (C : Ω → ℝ) (hC : StronglyMeasurable[F s] C)
    (hv : v =ᵐ[energyMeasure μ H] (fun p => PredictableSteps.step s t C p • u p)) :
    (I).integral v =ᵐ[μ] (fun ω => C ω •
      ((I).integral (StoppedItoInputs.stop F μ H t u) ω - (I).integral (StoppedItoInputs.stop F μ H s u) ω)) := by
  have hz : (fun ω => (I).integral v ω - C ω •
      ((I).integral (StoppedItoInputs.stop F μ H t u) ω - (I).integral (StoppedItoInputs.stop F μ H s u) ω))
      =ᵐ[μ] (fun _ => (0:E)) := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    have hvp : scalarInput F μ H L v =ᵐ[energyMeasure μ H]
        (fun p => PredictableSteps.step s t C p • scalarInput F μ H L u p) := by
      filter_upwards [scalarInput_ae F μ H L v,scalarInput_ae F μ H L u,hv] with p h1 h2 h3
      rw [h1,h2,h3,map_smul,map_smul]
    have hh := SHEStochastic.UnboundedPastMultiplier.cell J hlocal
      (scalarInput F μ H L u) (scalarInput F μ H L v) s t hst C hC hvp
    have h0 := L.coeFn_compLpL ((I).integral v)
    have h1 := L.coeFn_compLpL ((I).integral (StoppedItoInputs.stop F μ H t u))
    have h2 := L.coeFn_compLpL ((I).integral (StoppedItoInputs.stop F μ H s u))
    rw [HeatTerminalNaturality.scalar_commutes] at h0 h1 h2
    change (J.integral (scalarInput F μ H L v) : Ω → ℝ) =ᵐ[μ] (fun ω => L ((I).integral v ω)) at h0
    change (J.integral (scalarInput F μ H L (StoppedItoInputs.stop F μ H t u)) : Ω → ℝ) =ᵐ[μ]
      (fun ω => L ((I).integral (StoppedItoInputs.stop F μ H t u) ω)) at h1
    change (J.integral (scalarInput F μ H L (StoppedItoInputs.stop F μ H s u)) : Ω → ℝ) =ᵐ[μ]
      (fun ω => L ((I).integral (StoppedItoInputs.stop F μ H s u) ω)) at h2
    rw [scalarInput_stop F μ H L u t] at h1
    rw [scalarInput_stop F μ H L u s] at h2
    filter_upwards [h0,h1,h2,hh] with ω h0 h1 h2 hh
    change L (_ - _) = 0
    rw [map_sub,map_smul,map_sub,←h0,←h1,←h2,hh]
    simp only [smul_eq_mul,sub_self]
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

end HeatHilbertPastMultiplier
#check @HeatHilbertPastMultiplier.scalarInput_ae
#print axioms HeatHilbertPastMultiplier.scalarInput_ae
#check @HeatHilbertPastMultiplier.scalarInput_stop
#print axioms HeatHilbertPastMultiplier.scalarInput_stop
#check @HeatHilbertPastMultiplier.cell
#print axioms HeatHilbertPastMultiplier.cell
