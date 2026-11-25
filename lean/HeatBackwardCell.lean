import HeatMildRestart
import HeatTerminalBrownian
import SHE.IntervalTimeMeasure

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatBackwardCell
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

def drift (t b : ℝ≥0) (q : E) : E :=
  ∫ s in Ioc t b, S (s-t) (M (S (b-s) q)) ∂timeMeasure H

def state (W : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (q : E) (t : ℝ≥0) (ω : Ω) : E :=
  (W t ω-W a ω) • S (b-t) q + drift H S M t b q

def noiseInput (t b : ℝ≥0) (q : E) : Process (E := E) F μ H :=
  StoppedItoInputs.stop F μ H b (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q)) -
    StoppedItoInputs.stop F μ H t (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q))

theorem terminal (hzero : S 0 = ContinuousLinearMap.id ℝ E) (W : ℝ≥0 → Ω → ℝ)
    (a b : ℝ≥0) (q : E) (ω : Ω) :
    state H S M W a b q b ω = (W b ω-W a ω) • q := by
  simp [state,drift,hzero]

theorem left_state (W : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (q : E) (ω : Ω) :
    state H S M W a b q a ω = drift H S M a b q := by
  simp only [state,sub_self,zero_smul,zero_add]

theorem kernel_constant (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    {t s b : ℝ≥0} (hts : t ≤ s) (hsb : s ≤ b) (q : E) :
    S (s-t) (S (b-s) q) = S (b-t) q := by
  have htime : (s-t)+(b-s) = b-t := by rw [add_comm]; exact tsub_add_tsub_cancel hsb hts
  have hh := congrArg (fun L : E →L[ℝ] E => L q) (hsem (s-t) (b-s))
  rw [htime] at hh
  exact hh.symm

theorem noiseInput_ae (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    {t b : ℝ≥0} (htb : t ≤ b) (q : E) :
    noiseInput F μ H S t b q =ᵐ[energyMeasure μ H]
      (fun p => (Ioc t b).indicator (fun s => S (s-t) (S (b-s) q)) p.1) := by
  have hn : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 ≠ b :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne b)
  have hnt : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 ≠ t :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne t)
  filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub
    (StoppedItoInputs.stop F μ H b (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q)))
    (StoppedItoInputs.stop F μ H t (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q)))),
    StoppedItoInputs.stop_ae F μ H b (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q)),
    StoppedItoInputs.stop_ae F μ H t (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q)),
    RotatedCylindricalCoordinates.constant_ae F μ H (S (b-t) q),hn,hnt] with p hd hb ht hq hn hnt
  dsimp only [noiseInput]
  rw [hd]
  simp only [Pi.sub_apply,hb,ht,Set.indicator_apply,StoppedItoInputs.before,Set.mem_setOf_eq,NNReal.coe_lt_coe]
  by_cases hp : p.1 < b <;> by_cases ht' : p.1 < t
  · have hh : p.1 ∉ Ioc t b := fun h => (not_lt_of_ge h.1.le) ht'
    simp only [hp,ht',ite_true,hh,ite_false,sub_self]
  · have htp : t < p.1 := lt_of_le_of_ne (le_of_not_gt ht') hnt.symm
    have hm : p.1 ∈ Ioc t b := ⟨htp,hp.le⟩
    simp only [hp,ht',ite_true,ite_false,hm,sub_zero,hq]
    exact (kernel_constant S hsem htp.le hp.le q).symm
  · exact False.elim (hp (ht'.trans_le htb))
  · have hh : p.1 ∉ Ioc t b := by
      intro h
      exact hn (le_antisymm h.2 (le_of_not_gt hp))
    simp only [hp,ht',ite_true,ite_false,hh,sub_self]

include basis J in
theorem noise_integral (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    {t b : ℝ≥0} (htb : t ≤ b) (hbH : b ≤ H) (q : E) :
    (I).integral (noiseInput F μ H S t b q) =ᵐ[μ]
      (fun ω => (W b ω-W t ω) • S (b-t) q) := by
  unfold noiseInput
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub
    ((I).integral (StoppedItoInputs.stop F μ H b (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q))))
    ((I).integral (StoppedItoInputs.stop F μ H t (RotatedCylindricalCoordinates.constant F μ H (S (b-t) q)))),
    HeatTerminalBrownian.constant_integral F μ H basis J (S (b-t) q) b,
    HeatTerminalBrownian.constant_integral F μ H basis J (S (b-t) q) t,
    hW b hbH,hW t (htb.trans hbH)] with ω hd hb ht hwb hwt
  rw [hd]
  simp only [Pi.sub_apply,hb,ht,hwb,hwt,sub_smul]

include basis J in
theorem mild_equation (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    {a t b : ℝ≥0} (htb : t ≤ b) (hbH : b ≤ H) (q : E) :
    state H S M W a b q t =ᵐ[μ]
      (fun ω => S (b-t) ((W b ω-W a ω) • q) + drift H S M t b q -
        (I).integral (noiseInput F μ H S t b q) ω) := by
  filter_upwards [noise_integral F μ H S basis J W hW htb hbH q] with ω hω
  rw [hω,map_smul]
  unfold state
  module

end HeatBackwardCell
#check @HeatBackwardCell.terminal
#print axioms HeatBackwardCell.terminal
#check @HeatBackwardCell.left_state
#print axioms HeatBackwardCell.left_state
#check @HeatBackwardCell.kernel_constant
#print axioms HeatBackwardCell.kernel_constant
#check @HeatBackwardCell.noiseInput_ae
#print axioms HeatBackwardCell.noiseInput_ae
#check @HeatBackwardCell.noise_integral
#print axioms HeatBackwardCell.noise_integral
#check @HeatBackwardCell.mild_equation
#print axioms HeatBackwardCell.mild_equation
