import HeatHilbertFutureCenter
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatPastPairing
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

theorem conditional_pairing (a : ℝ≥0) (X Y Z : Lp E 2 μ)
    (hY : AEStronglyMeasurable[F a] Y μ) (hz : μ[(X : Ω → E) | F a]=ᵐ[μ] Z) :
    inner ℝ X Y=inner ℝ Z Y := by
  have hc := (Lp.memLp X).condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le a)
  have he : (condExpL2 E ℝ (F.le a) X : Lp E 2 μ)=Z := by
    apply Lp.ext
    simpa only [Lp.toLp_coeFn] using hc.trans hz
  rw [← he]
  exact (inner_condExpL2_eq_inner_fun (F.le a) X Y hY).symm

variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]

theorem future_orthogonal (I : StandardTerminalIto (C := C) (E := E) F μ H)
    (hl : StandardTerminalPastLocality I) (a : ℝ≥0) (u : Process (E := C) F μ H)
    (Y : Lp E 2 μ) (hY : AEStronglyMeasurable[F a] Y μ) :
    inner ℝ (I.integral (PastItoInputs.post F μ H a u)) Y=0 := by
  have hz : μ[(I.integral (PastItoInputs.post F μ H a u) : Ω → E) | F a]=ᵐ[μ] (0 : Lp E 2 μ) :=
    (HeatHilbertFutureCenter.condExp_post_zero I hl a u).trans (Lp.coeFn_zero E 2 μ).symm
  rw [conditional_pairing a _ Y 0 hY hz]
  simp

end HeatPastPairing
#check @HeatPastPairing.conditional_pairing
#print axioms HeatPastPairing.conditional_pairing
#check @HeatPastPairing.future_orthogonal
#print axioms HeatPastPairing.future_orthogonal
