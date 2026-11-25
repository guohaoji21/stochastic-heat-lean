import HeatVariationalForwardModel
import HeatBackwardLp
import HeatBaseNontrivial

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatBackwardModel
open MeasureTheory SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : Nontrivial Base := HeatBaseNontrivial.nontrivial
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ H)
  (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (g : Base)

abbrev path := HeatBackwardProcess.state family family_continuous family_contraction M H W t N g

structure Solution where
  noise : Process (E := Base) F μ H
  noise_formula : noise=ᵐ[energyMeasure μ H] HeatBackwardNoise.raw family family_continuous family_contraction M W t N g
  value : ℝ≥0 → Lp Base 2 μ
  value_continuous : Continuous value
  value_path : ∀ a, a≤H → value a=ᵐ[μ] path H M W t N g a
  value_adapted : ∀ a, AEStronglyMeasurable[F a] (value a) μ
  path_continuous : ∀ ω, Continuous (fun a => path H M W t N g a ω)
  path_adapted : StronglyAdapted F (path H M W t N g)
  path_predictable : StronglyMeasurable[F.predictable] (Function.uncurry (path H M W t N g))
  terminal : ∀ ω, path H M W t N g H ω=HeatBrownianProducts.products W t N ω • g
  maximum_energy : Integrable (fun ω => HeatPathMaximum.value H (path H M W t N g) ω^2) μ
  noise_energy : Integrable (fun p : ℝ≥0 × Ω => ‖noise p‖^2) (energyMeasure μ H)
  mild_equation : ∀ a b, a≤b → b≤H → value a=((family (b-a)).compLpL 2 μ) (value b)+
    HeatActualCellEnergy.drift F μ H family family_continuous family_contraction M a b noise-
    I.integral (HeatBackwardKernel.input F μ H family family_continuous family_contraction (ContinuousLinearMap.id ℝ Base) a b noise)

variable {κ : Type*} [Countable κ]
  (basis : HilbertBasis κ ℝ Base)
  (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => SHE.RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem exists_solution (hlocal : SHE.StandardTerminalPastLocality J)
    (hW : ∀ s : ℝ≥0, s≤H → J.integral (SHE.StoppedItoInputs.stop F μ H s R)=ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (ht : Monotone t) (ht0 : t 0=0) (hN : 1≤N)
    (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=H)
    (hP : ∀ n, n≤N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ) :
    Nonempty (Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) W t N g) := by
  let v := HeatBackwardNoise.process family family_continuous family_contraction M F μ H W t N g hP
  obtain ⟨Z,hZc,hZr,hZa,hzc,hza,⟨D,hDm,hD0,hDb⟩,hz⟩ :=
    HeatBackwardLp.exists_solution F μ H family family_continuous family_contraction M basis J paperHeat_zero family_semigroup
      hlocal W hW hWa hWc t ht ht0 N hN hstep hTN g hP
  refine ⟨⟨v,HeatBackwardNoise.process_ae family family_continuous family_contraction M F μ H W t N g hP,
    Z,hZc,hZr,hZa,hzc,hza,SHE.ContinuousPredictable.stronglyMeasurable F _ hza hzc,?_,?_,?_,hz⟩⟩
  · intro ω
    have he := HeatBackwardProcess.terminal family family_continuous family_contraction M (H := H) paperHeat_zero W t N hN hstep g ω
    rw [hTN] at he
    exact he
  · exact HeatPathMaximum.integrable_square μ H _
      (fun a => (hza a).measurable.mono (F.le a) le_rfl) hzc D hDm hD0 hDb
  · exact (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)).norm.integrable_sq

end HeatBackwardModel
#check @HeatBackwardModel.exists_solution
#print HeatBackwardModel.Solution
#print HeatBackwardModel.exists_solution
#print axioms HeatBackwardModel.exists_solution
