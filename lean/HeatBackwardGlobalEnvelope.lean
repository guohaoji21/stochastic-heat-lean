import HeatBackwardNoise
import HeatBackwardEnvelope
import HeatFiniteEnvelopes

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatBackwardGlobalEnvelope
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns HeatCovarianceOperator
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

include hS hcontr in
theorem exists_envelope (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    (hWa : ∀ t, StronglyMeasurable[F t] (W t)) (hc : ∀ ω, Continuous (fun t => W t ω))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1 ≤ N) (hT : t N ≤ H) (g : E)
    (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ) :
    ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧
      ∀ s : ℝ≥0, s ≤ t N → ∀ ω, ‖HeatBackwardProcess.state S hS hcontr M H W t N g s ω‖ ≤ D ω := by
  let I := {j // j ∈ Finset.Icc 1 N}
  have hh (j : I) : ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧
      ∀ s : ℝ≥0, t (j-1) ≤ s → s ≤ t j → ∀ ω,
        ‖HeatBackwardNodes.cellState S hS hcontr M H W t N g j s ω‖ ≤ D ω := by
    exact HeatBackwardEnvelope.cell_envelope S hS hcontr M F μ H J hlocal W hW hWa hc
      (ht (Nat.sub_le _ _)) ((ht (Finset.mem_Icc.mp j.property).2).trans hT)
      (HeatBackwardNoise.coefficient W t j) (HeatBackwardNoise.coefficient_strong F μ W t N hP j)
      (HeatBackwardNoise.coefficient_memLp F μ W t N hP j)
      (HeatBackwardChain.stateAt (covariance S hS hcontr M) (fun k => t k-t (k-1)) N g j)
  choose D hDm hD0 hDb using hh
  let d (j : ℕ) (ω : Ω) : ℝ := if hj : j ∈ Finset.Icc 1 N then D ⟨j,hj⟩ ω else 0
  have hd (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
      d j = D ⟨j,Finset.mem_Icc.mpr ⟨hj,hjN⟩⟩ := by
    funext ω
    dsimp [d]
    rw [dif_pos (Finset.mem_Icc.mpr ⟨hj,hjN⟩)]
  have hdm (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) : MemLp (d j) 2 μ := by
    rw [hd j hj hjN]
    exact hDm _
  have hd0 (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (ω : Ω) : 0 ≤ d j ω := by
    rw [hd j hj hjN]
    exact hD0 _ ω
  have hdb (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (s : ℝ≥0) (hlo : t (j-1) ≤ s) (hhi : s ≤ t j) (ω : Ω) :
      ‖HeatBackwardNodes.cellState S hS hcontr M H W t N g j s ω‖ ≤ d j ω := by
    rw [hd j hj hjN]
    exact hDb ⟨j,Finset.mem_Icc.mpr ⟨hj,hjN⟩⟩ s hlo hhi ω
  refine ⟨fun ω => ∑ j ∈ Finset.Icc 1 N, d j ω, HeatFiniteEnvelopes.sum_memLp μ d N hdm, ?_, ?_⟩
  · intro ω
    exact Finset.sum_nonneg (fun j hj => hd0 j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 ω)
  · intro s hs ω
    have hx0 : t 0 ≤ s := by rw [ht0]; exact zero_le
    have he := HeatFiniteEnvelopes.paste_bound t
      (fun j s ω => HeatBackwardNodes.cellState S hS hcontr M H W t N g j s ω) N d hd0 hdb
      (N-1) (by omega) s hx0 (by simpa only [Nat.sub_add_cancel hN] using hs) ω
    simpa only [HeatBackwardProcess.state,Nat.sub_add_cancel hN] using he

end HeatBackwardGlobalEnvelope
#check @HeatBackwardGlobalEnvelope.exists_envelope
#print HeatBackwardGlobalEnvelope.exists_envelope
#print axioms HeatBackwardGlobalEnvelope.exists_envelope
