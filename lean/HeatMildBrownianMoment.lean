import HeatMildRestart
import HeatVectorConditionalCross
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatMildBrownianMoment
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open HeatMildSolution HeatPredictableStateInput
open scoped NNReal ENNReal

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

include hsem in
theorem cross_bracket (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0} (hab : a ≤ b)
    (g : E) (u : Process (E := E) F μ H) :
    μ[(fun ω => (J.integral (StoppedItoInputs.stop F μ H b R) ω -
      J.integral (StoppedItoInputs.stop F μ H a R) ω) • value F μ H S hS hcontr M I g u b ω) | F a] =ᵐ[μ]
      μ[(fun ω => ∫ s in Set.Ioc a b, S (b-s) (M (u (s,ω))) ∂timeMeasure H) | F a] := by
  let X : Ω → ℝ := fun ω => J.integral (StoppedItoInputs.stop F μ H b R) ω -
    J.integral (StoppedItoInputs.stop F μ H a R) ω
  let V₀ := value F μ H S hS hcontr M I g u a
  let A := S (b-a)
  let V : Ω → E := fun ω => A (V₀ ω)
  let N : Ω → E := fun ω => (I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)) ω -
    (I).integral (StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u)) ω
  have hX : MemLp X 2 μ := (Lp.memLp (J.integral (StoppedItoInputs.stop F μ H b R))).sub
    (Lp.memLp (J.integral (StoppedItoInputs.stop F μ H a R)))
  have hN : MemLp N 2 μ :=
    (Lp.memLp ((I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)))).sub
    (Lp.memLp ((I).integral (StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u))))
  have hV : MemLp V 2 μ := A.comp_memLp' (Lp.memLp V₀)
  have hXV : Integrable (fun ω => X ω • V ω) μ := memLp_one_iff_integrable.mp (hX.smul hV)
  have hXN : Integrable (fun ω => X ω • N ω) μ := memLp_one_iff_integrable.mp (hX.smul hN)
  obtain ⟨Z,hZ,hrep⟩ := value_adapted F μ H S hS hcontr M I g u a
  have hVm : AEStronglyMeasurable[F a] V μ :=
    (A.continuous.comp_stronglyMeasurable hZ).aestronglyMeasurable.congr (hrep.fun_comp A).symm
  have hzero : μ[(fun ω => X ω • V ω) | F a] =ᵐ[μ] (fun _ => (0:E)) := by
    have hp := condExp_smul_of_aestronglyMeasurable_right (hX.integrable one_le_two) hXV hVm
    have hx := HeatHilbertFutureCenter.condExp_increment_zero J hlocal hab R
    filter_upwards [hp,hx] with ω hp hx
    change μ[(fun ω => X ω • V ω) | F a] ω = _
    change μ[(fun ω => X ω • V ω) | F a] ω = μ[X | F a] ω • V ω at hp
    change μ[X | F a] ω = 0 at hx
    exact hp.trans (by rw [hx,zero_smul])
  have hd : (value F μ H S hS hcontr M I g u b : Ω → E) =ᵐ[μ] (fun ω => V ω + N ω) := by
    rw [HeatMildRestart.restart F μ H S hS hcontr M hsem basis J hab]
    filter_upwards [Lp.coeFn_add ((A.compLpL 2 μ) V₀)
      ((I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)) -
        (I).integral (StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u))),
      A.coeFn_compLpL V₀,
      Lp.coeFn_sub ((I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)))
        ((I).integral (StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u)))] with ω hs ha hn
    rw [hs]
    simp only [Pi.add_apply,ha,hn,Pi.sub_apply]
    rfl
  have hd' : (fun ω => X ω • value F μ H S hS hcontr M I g u b ω) =ᵐ[μ]
      (fun ω => X ω • V ω + X ω • N ω) := by
    filter_upwards [hd] with ω hω
    rw [hω,smul_add]
  have hcross := HeatVectorConditionalCross.conditional_cross F μ H basis J hlocal hab
    (factor F μ H S hS hcontr M b u)
  have hf := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (factor_ae F μ H S hS hcontr M b u)
  have hbracket : (fun ω => ∫ s in Set.Ioc a b, factor F μ H S hS hcontr M b u (s,ω) ∂timeMeasure H) =ᵐ[μ]
      (fun ω => ∫ s in Set.Ioc a b, S (b-s) (M (u (s,ω))) ∂timeMeasure H) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hf] with ω hω
    exact integral_congr_ae (ae_restrict_of_ae hω)
  have hc := hcross.trans (condExp_congr_ae (m := F a) hbracket)
  have he := condExp_congr_ae (m := F a) hd'
  have ha := condExp_add hXV hXN (F a)
  filter_upwards [he,ha,hzero,hc] with ω he ha hz hc
  change μ[(fun ω => X ω • value F μ H S hS hcontr M I g u b ω) | F a] ω = _
  change μ[(fun ω => X ω • V ω + X ω • N ω) | F a] ω = _ at ha
  rw [ha] at he
  simp only [Pi.add_apply] at he
  rw [hz,zero_add] at he
  exact he.trans hc

end HeatMildBrownianMoment
#check @HeatMildBrownianMoment.cross_bracket
#print axioms HeatMildBrownianMoment.cross_bracket
