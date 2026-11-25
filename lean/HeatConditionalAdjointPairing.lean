import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Ring
import HeatBackwardDrift
import HeatCovarianceAdjoint
import HeatCanonicalRestartMoments
import HeatPaperCovariance
import HeatWeightedBrownian

set_option autoImplicit false
noncomputable section

namespace HeatConditionalAdjointPairing

open MeasureTheory Filter

/-- The scalar pairing on one partition cell. The two conditional moments
are supplied by the restarted forward equation. Integrability is stated for
each of the two terms of the decomposed Brownian increment. -/
theorem split_increment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : MeasurableSpace Ω) (past elapsed remaining Y : Ω → ℝ) (mean mixed : ℝ)
    (hpast : AEStronglyMeasurable[m] past μ)
    (helapsed : AEStronglyMeasurable[m] elapsed μ)
    (hY : Integrable Y μ) (hmixedY : Integrable (remaining * Y) μ)
    (hfirst : Integrable ((past * elapsed) * Y) μ)
    (hsecond : Integrable (past * (remaining * Y)) μ)
    (hmean : μ[Y | m] =ᵐ[μ] fun _ => mean)
    (hmixed : μ[remaining * Y | m] =ᵐ[μ] fun _ => mixed) :
    μ[(fun ω => past ω * (elapsed ω + remaining ω) * Y ω) | m] =ᵐ[μ]
      fun ω => past ω * (elapsed ω * mean + mixed) := by
  have hsplit : (fun ω => past ω * (elapsed ω + remaining ω) * Y ω) =
      (past * elapsed) * Y + past * (remaining * Y) := by
    funext ω
    change _ = past ω * elapsed ω * Y ω + past ω * (remaining ω * Y ω)
    ring
  rw [hsplit]
  have h₁ := condExp_mul_of_aestronglyMeasurable_left (hpast.mul helapsed) hfirst hY
  have h₂ := condExp_mul_of_aestronglyMeasurable_left hpast hsecond hmixedY
  filter_upwards [condExp_add hfirst hsecond m, h₁, h₂, hmean, hmixed]
    with ω hadd hleft hright hμ₁ hμ₂
  rw [hadd]
  change μ[(past * elapsed) * Y | m] ω + μ[past * (remaining * Y) | m] ω = _
  rw [hleft, hright]
  change past ω * elapsed ω * μ[Y | m] ω + past ω * μ[remaining * Y | m] ω = _
  rw [hμ₁, hμ₂]
  ring

open scoped NNReal

/-- The conditional pairing on the cell `(a,b]` obtained from the restarted
forward mean and Brownian cross moment. The right side uses the actual
backward cell from the construction. -/
theorem cell_pairing {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (m : MeasurableSpace Ω) {H a t b : ℝ≥0}
    (htb : t ≤ b) (hbH : b ≤ H)
    (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun r => S r x))
    (hcontr : ∀ r x, ‖S r x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
    (hSsym : ∀ r x y, inner ℝ (S r x) y = inner ℝ x (S r y))
    (hMsym : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (W : ℝ≥0 → Ω → ℝ) (P : Ω → ℝ) (Y : Ω → E) (f q : E)
    (hP : AEStronglyMeasurable[m] P μ)
    (hW : AEStronglyMeasurable[m] (fun ω => W t ω - W a ω) μ)
    (hY : Integrable Y μ)
    (hWY : Integrable (fun ω => (W b ω - W t ω) • Y ω) μ)
    (hfirst : Integrable (fun ω => (P ω * (W t ω - W a ω)) * inner ℝ q (Y ω)) μ)
    (hsecond : Integrable (fun ω => P ω * ((W b ω - W t ω) * inner ℝ q (Y ω))) μ)
    (hmean : μ[Y | m] =ᵐ[μ] fun _ => S (b-t) f)
    (hmixed : μ[(fun ω => (W b ω - W t ω) • Y ω) | m] =ᵐ[μ] fun _ =>
      (↑(b-t) : ℝ) • HeatCovarianceOperator.covariance S hS hcontr M (b-t) f) :
    μ[(fun ω => P ω * (W b ω - W a ω) * inner ℝ q (Y ω)) | m] =ᵐ[μ]
      fun ω => P ω * inner ℝ (HeatBackwardCell.state H S M W a b q t ω) f := by
  let L := innerSL ℝ q
  let X : Ω → ℝ := fun ω => W t ω - W a ω
  let R : Ω → ℝ := fun ω => W b ω - W t ω
  let V : Ω → ℝ := L ∘ Y
  let K := HeatCovarianceOperator.covariance S hS hcontr M (b-t)
  have hmul : R * V = L ∘ (fun ω => (W b ω - W t ω) • Y ω) := by
    funext ω
    change R ω * L (Y ω) = L (R ω • Y ω)
    rw [map_smul, smul_eq_mul]
  have hsmean : μ[V | m] =ᵐ[μ] fun _ => L (S (b-t) f) :=
    (L.comp_condExp_comm (m := m) hY).symm.trans (hmean.fun_comp L)
  have hsmix : μ[R * V | m] =ᵐ[μ] fun _ => L ((↑(b-t) : ℝ) • K f) := by
    rw [hmul]
    exact (L.comp_condExp_comm (m := m) hWY).symm.trans (hmixed.fun_comp L)
  have hR : Integrable (R * V) μ := by
    rw [hmul]
    exact L.integrable_comp hWY
  have hfirst' : Integrable ((P * X) * V) μ := hfirst
  have hsecond' : Integrable (P * (R * V)) μ := hsecond
  have hsplit := @split_increment Ω mΩ μ m P X R V _ _ hP hW
    (L.integrable_comp hY) hR hfirst' hsecond' hsmean hsmix
  have heq : (fun ω => P ω * (W b ω - W a ω) * inner ℝ q (Y ω)) =
      (fun ω => P ω * (X ω + R ω) * V ω) := by
    funext ω
    dsimp [X, R, V, L]
    ring
  rw [heq]
  filter_upwards [hsplit] with ω hω
  change μ[(fun ω => P ω * (X ω + R ω) * V ω) | m] ω = _ at hω
  rw [hω, HeatBackwardCell.state, HeatBackwardDrift.drift_covariance S hS hcontr M htb hbH]
  simp only [X, K, L, innerSL_apply_apply, real_inner_smul_left, real_inner_smul_right,
    inner_add_left]
  rw [hSsym, HeatCovarianceAdjoint.covariance_inner S hS hcontr M hSsym hMsym]

open SHE HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped ENNReal

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate
local notation "Ω" => C(ℝ≥0, ℝ)

local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure; infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

/-- Restart the concrete uncontrolled forward heat equation with deterministic
state `f` at an interior time of a cell, and compute the conditional pairing
with the final increment on that cell. -/
theorem canonical_restart_pairing {H a t b : ℝ≥0} (hat : a ≤ t) (htb : t < b) (hbH : b ≤ H)
    (β : ℝ → ℝ) (hβ : AEStronglyMeasurable β baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure, ‖β x‖ ≤ 1) (P : Ω → ℝ) (f q : Base) :
    letI : MeasurableSpace Ω :=
      HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    let r := b - t
    let Fs := HeatShiftedBrownian.filtration F t
    let J := HeatShiftedNative.scalar F μ W HeatCanonicalUsual56.coordinate_filtered_brownian
      (fun ω => ω.continuous) t r
    let I := HeatTerminalNaturality.integral Fs μ r HeatCanonicalPhysicalIto.basis J
    StronglyMeasurable[F a] P → MemLp P 2 μ →
    ∃ (hU : IsStronglyProgressive Fs (fun (_ : ℝ≥0) (_ : Ω) => (0 : Base)))
      (hE : Integrable (fun _p : ℝ≥0 × Ω => ‖(0 : Base)‖ ^ 2) (SHE.PredictableL2.energyMeasure μ r))
      (sol : HeatVariationalForwardModel.Solution Fs μ r (noise β hβ hbound) I (fun _ _ => 0) hU hE f),
      let Y := sol.weak.path r
      MemLp Y 2 μ ∧
        μ[(fun ω => P ω * (W b ω - W a ω) * inner ℝ q (Y ω)) | F t] =ᵐ[μ]
          fun ω => P ω * inner ℝ (HeatBackwardCell.state H family (noise β hβ hbound) W a b q t ω) f := by
  letI : MeasurableSpace Ω :=
    HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  dsimp only
  intro hP hPm
  let r := b - t
  let M := noise β hβ hbound
  let K := HeatPaperCovariance.K β hβ hbound
  obtain ⟨hU, hE, sol, hinit, hmom⟩ := HeatCanonicalRestartMoments.exists_solution_and_moments
    t r (tsub_pos_of_lt htb) β hβ hbound f
  let Y := sol.weak.path r
  have hY : MemLp Y 2 μ := (Lp.memLp _).ae_eq (sol.weak.path_version r le_rfl).symm
  refine ⟨hU, hE, sol, hY, ?_⟩
  have htime : t + r = b := by rw [add_comm]; exact tsub_add_cancel_of_le htb.le
  obtain ⟨hμ, hXμ⟩ := hmom 0 r (by positivity) le_rfl
  simp only [add_zero, tsub_zero, NNReal.coe_zero, htime] at hμ hXμ
  have hmean : μ[Y | F t] =ᵐ[μ] fun _ => family r f := by
    filter_upwards [hμ, hinit] with ω h₁ h₂
    exact h₁.trans (congrArg (family r) h₂)
  have hcross : μ[(fun ω => (W b ω - W t ω) • Y ω) | F t] =ᵐ[μ]
      fun _ => (r : ℝ) • K r f := by
    filter_upwards [hXμ, hinit] with ω h₁ h₂
    exact h₁.trans (by
      rw [h₂]
      exact congrArg ((r : ℝ) • ·) (HeatCovarianceOperator.covariance_apply
        family family_continuous family_contraction M r f).symm)
  have hFt := (F).mono hat
  have hPt := hP.mono hFt
  have hWa (s : ℝ≥0) : StronglyMeasurable[F s] (W s) :=
    HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted s
  let J := HeatCanonicalNative.scalar H
  have hweighted {u v : ℝ≥0} (huv : u ≤ v) (hvH : v ≤ H) (Q : Ω → ℝ)
      (hQ : StronglyMeasurable[F u] Q) (hQm : MemLp Q 2 μ) :
      MemLp (fun ω => Q ω * (W v ω - W u ω)) 2 μ :=
    HeatWeightedBrownian.weighted_increment_memLp F μ H J (HeatCanonicalNative.locality H)
      W (HeatCanonicalNative.coordinate H) huv hvH Q hQ hQm
  have hleft := hweighted hat (htb.le.trans hbH) P hP hPm
  have hright := hweighted htb.le hbH P hPt hPm
  have hR : MemLp (fun ω => W b ω - W t ω) 2 μ := by
    simpa only [one_mul] using hweighted htb.le hbH (fun _ => 1) stronglyMeasurable_const (memLp_const 1)
  have hscalar : MemLp (fun ω => inner ℝ q (Y ω)) 2 μ := (innerSL ℝ q).comp_memLp' hY
  have hWY : Integrable (fun ω => (W b ω - W t ω) • Y ω) μ :=
    memLp_one_iff_integrable.mp (hR.smul hY)
  have hfirst : Integrable (fun ω => P ω * (W t ω - W a ω) * inner ℝ q (Y ω)) μ :=
    memLp_one_iff_integrable.mp (hleft.smul hscalar)
  have hrightPair : Integrable (fun ω => (P ω * (W b ω - W t ω)) * inner ℝ q (Y ω)) μ :=
    memLp_one_iff_integrable.mp (hright.smul hscalar)
  have hsecond : Integrable (fun ω => P ω * ((W b ω - W t ω) * inner ℝ q (Y ω))) μ := by
    simpa only [mul_assoc] using hrightPair
  exact cell_pairing μ (F t) htb.le hbH family family_continuous family_contraction M
    (fun s => HeatPaperAdjoint.paper_heat_inner s)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (HeatMultiplierAdjoint.scalar_multiplier_self_adjoint baseMeasure β hβ hbound))
    W P Y f q hPt.aestronglyMeasurable
    ((hWa t).sub ((hWa a).mono hFt)).aestronglyMeasurable
    (hY.integrable one_le_two) hWY hfirst hsecond hmean hcross

end HeatConditionalAdjointPairing

#print axioms HeatConditionalAdjointPairing.split_increment
#print axioms HeatConditionalAdjointPairing.cell_pairing
#print axioms HeatConditionalAdjointPairing.canonical_restart_pairing
