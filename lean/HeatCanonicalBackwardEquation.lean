import HeatCanonicalLocalBackwardEquation
import HeatBackwardCellGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace HeatCanonicalBackwardEquation

open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "P" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0, ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure P := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (HilbertColumns.Space Unit ℝ) := ⟨rfl⟩

variable {κ E : Type*} [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The canonical linear backward equation for bounded operators on any
finite horizon. This supplies a backward equation on each finite Galerkin
space, with arbitrary adapted square-integrable terminal data. -/
theorem exists_solution (H : ℝ≥0) (basis : HilbertBasis κ ℝ E) (A B : E →L[ℝ] E)
    (η : Lp E 2 P) (hη : AEStronglyMeasurable[F H] (η : C(ℝ≥0, ℝ) → E) P) :
    Nonempty (HeatLocalBackwardEquation.Solution
      (HeatTerminalNaturality.integral F P H basis (HeatCanonicalNative.scalar H)) A B 0 H η) := by
  let J := HeatTerminalNaturality.integral F P H basis (HeatCanonicalNative.scalar H)
  have hJ : StandardTerminalPastLocality J :=
    HeatTerminalNaturality.locality F P H basis (HeatCanonicalNative.scalar H) (HeatCanonicalNative.locality H)
  obtain ⟨δ, hδ, hshort⟩ := HeatCanonicalLocalBackwardEquation.exists_step_size A B
  obtain ⟨n, hn⟩ := exists_nat_gt ((H : ℝ) / δ)
  have hnpos : (0 : ℝ) < n := (div_nonneg H.property hδ.le).trans_lt hn
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
  have hlen : (H : ℝ) / n ≤ δ := by
    apply (div_le_iff₀ hnpos).mpr
    simpa only [mul_comm] using ((div_lt_iff₀ hδ).mp hn).le
  let t (k : ℕ) : ℝ≥0 := k * (H / (n : ℝ≥0))
  have ht₀ : t 0 = 0 := by simp [t]
  have htn : t n = H := by dsimp [t]; rw [mul_comm, div_mul_cancel₀ _ hn0]
  have hmono : Monotone t := by
    intro i j hij
    dsimp [t]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hstep (k : ℕ) : ((t (k + 1) : ℝ≥0) : ℝ) - t k ≤ δ := by
    suffices he : ((t (k + 1) : ℝ≥0) : ℝ) - t k = (H : ℝ) / n by rwa [he]
    dsimp [t]
    push_cast
    ring
  have hlocal {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H) (hlen : (b : ℝ) - a ≤ δ)
      (ξ : Lp E 2 P) (hξ : AEStronglyMeasurable[F b] (ξ : C(ℝ≥0, ℝ) → E) P) :
      Nonempty (HeatLocalBackwardEquation.Solution J A B a b ξ) :=
    HeatCanonicalLocalBackwardEquation.exists_solution H basis A B hab hb
      (hshort _ (sub_nonneg.mpr (by exact_mod_cast hab)) hlen) ξ hξ
  have hprefix (k : ℕ) (hk : k ≤ n) (ξ : Lp E 2 P)
      (hξ : AEStronglyMeasurable[F (t k)] (ξ : C(ℝ≥0, ℝ) → E) P) :
      Nonempty (HeatLocalBackwardEquation.Solution J A B 0 (t k) ξ) := by
    induction k generalizing ξ with
    | zero =>
      apply hlocal (show (0 : ℝ≥0) ≤ t 0 from bot_le) ((hmono hk).trans_eq htn) _ ξ hξ
      simpa only [ht₀, NNReal.coe_zero, sub_zero] using hδ.le
    | succ k ih =>
      have hkk : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
      obtain ⟨R⟩ := hlocal hkk ((hmono hk).trans_eq htn) (hstep k) ξ hξ
      obtain ⟨L⟩ := ih ((Nat.le_succ k).trans hk) (HeatBackwardDriver.state (t (k + 1)) ξ R.drift (t k))
        (HeatBackwardDriver.state_adapted (t (k + 1)) ξ R.drift (t k))
      exact ⟨HeatBackwardCellGluing.glue J hJ (show (0 : ℝ≥0) ≤ t k from bot_le) hkk ξ R L⟩
  simpa only [htn] using hprefix n le_rfl η (by rwa [htn])

end HeatCanonicalBackwardEquation

#print axioms HeatCanonicalBackwardEquation.exists_solution
