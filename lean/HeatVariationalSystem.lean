import HeatVariationalForwardModel
import HeatVariationalDuality
import HeatConstructedDuality
import HeatBackwardModel
import HeatPaperAdjoint
import HeatBaseNontrivial

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 3000000
noncomputable section
namespace HeatVariationalSystem
open MeasureTheory Filter SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : Nontrivial Base := HeatBaseNontrivial.nontrivial
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "R" => SHE.RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem exists_adjoint (hM : ‖M‖≤1) (hMsym : ∀ x y, inner ℝ (M x) y=inner ℝ x (M y))
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ) (hlocal : SHE.StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s≤H → J.integral (SHE.StoppedItoInputs.stop F μ H s R)=ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1≤N)
    (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=H) (g₀ g : Base)
    (hP : ∀ n, n≤N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ)
    (U : ℝ≥0 → Ω → HeatIntervalNormalization.Base) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))
    (sol : HeatVariationalForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g₀) :
    ∃ back : HeatBackwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) W t N g,
      inner ℝ (sol.weak.value H) (back.value H)=inner ℝ (sol.weak.value 0) (back.value 0)+
        (∫ p,inner ℝ (U p.1 p.2) (HeatBackwardModel.path H M W t N g p.1 p.2) ∂energyMeasure μ H) := by
  obtain ⟨back⟩ := HeatBackwardModel.exists_solution F μ H M W t N g basis J hlocal hW hWa hWc ht ht0 hN hstep hTN hP
  obtain ⟨Z,hZc,hZr,hdual⟩ := HeatVariationalDuality.exists_adjoint F μ H M basis J
    paperHeat_zero family_semigroup (fun r x y => HeatPaperAdjoint.paper_heat_inner r x y) hM hMsym hnull hlocal
    W hW hWa hWc t ht ht0 N hN hstep hTN g₀ g hP U hU hE sol
  have heq (a : ℝ≥0) (ha : a≤H) : Z a=back.value a := by
    apply Lp.ext
    exact (hZr a ha).trans (back.value_path a ha).symm
  rw [heq H le_rfl,heq 0 zero_le] at hdual
  exact ⟨back,hdual⟩

end HeatVariationalSystem
#check @HeatVariationalSystem.exists_adjoint
#print HeatVariationalSystem.exists_adjoint
#print axioms HeatVariationalSystem.exists_adjoint
