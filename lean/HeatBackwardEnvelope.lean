import HeatWeightedBrownianProcess
import HeatWeightedBackwardCell

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatBackwardEnvelope
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

include hS hcontr in
theorem drift_bound {H b : ℝ≥0} (hbH : b ≤ H) (q : E) (t : ℝ≥0) :
    ‖HeatBackwardCell.drift H S M t b q‖ ≤ (H:ℝ)*‖M‖*‖q‖ := by
  rw [HeatBackwardDrift.drift_all_times S hS hcontr M hbH q t,norm_smul]
  have hn : ‖((b-t:ℝ≥0):ℝ)‖ = ((b-t:ℝ≥0):ℝ) := Real.norm_of_nonneg (b-t).property
  rw [hn]
  have hk := (HeatCovarianceOperator.covariance S hS hcontr M (b-t)).le_of_opNorm_le
    (HeatCovarianceOperator.covariance_norm S hS hcontr M (b-t)) q
  have hr : ((b-t:ℝ≥0):ℝ) ≤ (H:ℝ) := by exact_mod_cast (tsub_le_self.trans hbH : b-t ≤ H)
  calc
    _ ≤ ((b-t:ℝ≥0):ℝ)*(‖M‖*‖q‖) := mul_le_mul_of_nonneg_left hk (b-t).property
    _ ≤ (H:ℝ)*(‖M‖*‖q‖) := mul_le_mul_of_nonneg_right hr (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

include hS hcontr in
theorem cell_envelope (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    (hWa : ∀ t, StronglyMeasurable[F t] (W t)) (hc : ∀ ω, Continuous (fun t => W t ω))
    {a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H) (C : Ω → ℝ)
    (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) (q : E) :
    ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧
      ∀ t : ℝ≥0, a ≤ t → t ≤ b → ∀ ω, ‖C ω • HeatBackwardCell.state H S M W a b q t ω‖ ≤ D ω := by
  obtain ⟨B,hB,hB0,hBb⟩ := HeatWeightedBrownianProcess.exists_envelope F μ H J hlocal W hW hWa hc hab hbH C hC hCm
  let D : Ω → ℝ := fun ω => ‖q‖*(B ω+((H:ℝ)*‖M‖) * |C ω|)
  have hD : MemLp D 2 μ := by
    simpa only [D,Real.norm_eq_abs,Pi.add_apply] using (hB.add (hCm.norm.const_mul ((H:ℝ)*‖M‖))).const_mul ‖q‖
  refine ⟨D,hD,fun ω => mul_nonneg (norm_nonneg q) (add_nonneg (hB0 ω) (by positivity)),?_⟩
  intro t hat htb ω
  have hBW : ‖C ω*(W t ω-W a ω)‖ ≤ B ω := by
    have hh := hBb t (htb.trans hbH) ω
    simpa only [HeatWeightedBrownianProcess.process,HeatWeightedBrownianProcess.clock,
      max_eq_right hat,min_eq_right htb] using hh
  calc
    _ = ‖(C ω*(W t ω-W a ω)) • S (b-t) q + C ω • HeatBackwardCell.drift H S M t b q‖ := by
      rw [HeatBackwardCell.state,smul_add,smul_smul]
    _ ≤ ‖(C ω*(W t ω-W a ω)) • S (b-t) q‖ + ‖C ω • HeatBackwardCell.drift H S M t b q‖ := norm_add_le _ _
    _ ≤ B ω*‖q‖ + |C ω| * ((H:ℝ)*‖M‖*‖q‖) := by
      apply add_le_add
      · rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (hcontr _ _) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hBW (norm_nonneg _))
      · rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (drift_bound S hS hcontr M hbH q t) (abs_nonneg _)
    _ = D ω := by dsimp [D]; ring

end HeatBackwardEnvelope
#check @HeatBackwardEnvelope.drift_bound
#print axioms HeatBackwardEnvelope.drift_bound
#check @HeatBackwardEnvelope.cell_envelope
#print axioms HeatBackwardEnvelope.cell_envelope
