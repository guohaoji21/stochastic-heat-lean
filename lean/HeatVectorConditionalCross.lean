import HeatTerminalBrownian
import HeatHilbertIntervalExact
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatVectorConditionalCross
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
  (b : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ T b J
local notation "R" => RawCylindricalCoordinates.row F μ T (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

local instance : IsFiniteMeasure (energyMeasure μ T) := by unfold energyMeasure; infer_instance

theorem process_integrable (u : Process (E := E) F μ T) : Integrable u (energyMeasure μ T) :=
  (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).integrable one_le_two

theorem interval_integrable (a c : ℝ≥0) (u : Process (E := E) F μ T) :
    Integrable (fun ω => ∫ s in Set.Ioc a c, u (s,ω) ∂timeMeasure T) μ := by
  have h := (process_integrable F μ T u).indicator ((measurableSet_Ioc : MeasurableSet (Set.Ioc a c)).preimage measurable_fst)
  have hh := h.integral_prod_right
  convert hh using 1
  funext ω
  rw [← integral_indicator measurableSet_Ioc]
  congr 1


theorem bracket_pairing (q : E) (a c : ℝ≥0) (u : Process (E := E) F μ T) :
    (fun ω => ∫ s in Set.Ioc a c, inner ℝ (RotatedCylindricalCoordinates.constant F μ T q (s,ω))
      (u (s,ω)) ∂timeMeasure T) =ᵐ[μ]
      (fun ω => inner ℝ q (∫ s in Set.Ioc a c, u (s,ω) ∂timeMeasure T)) := by
  have hq := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure T)).quasiMeasurePreserving.ae
    (RotatedCylindricalCoordinates.constant_ae F μ T q)
  have hu : ∀ᵐ ω ∂μ, Integrable (fun s => u (s,ω)) (timeMeasure T) :=
    (process_integrable F μ T u).swap.prod_right_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hq,hu] with ω hq hu
  calc
    _ = ∫ s in Set.Ioc a c, inner ℝ q (u (s,ω)) ∂timeMeasure T := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hq] with s hs
      exact congrArg (fun z : E => inner ℝ z (u (s,ω))) hs
    _ = _ := (innerSL ℝ q).integral_comp_comm hu.integrableOn

theorem conditional_cross (hlocal : StandardTerminalPastLocality J) {a c : ℝ≥0} (hac : a ≤ c)
    (u : Process (E := E) F μ T) :
    μ[(fun ω => (J.integral (stop F μ T c R) ω - J.integral (stop F μ T a R) ω) •
      ((I).integral (stop F μ T c u) ω - (I).integral (stop F μ T a u) ω)) | F a] =ᵐ[μ]
      μ[(fun ω => ∫ s in Set.Ioc a c, u (s,ω) ∂timeMeasure T) | F a] := by
  let X : Ω → ℝ := fun ω => J.integral (stop F μ T c R) ω - J.integral (stop F μ T a R) ω
  let Y : Ω → E := fun ω => (I).integral (stop F μ T c u) ω - (I).integral (stop F μ T a u) ω
  let Q : Ω → E := fun ω => ∫ s in Set.Ioc a c, u (s,ω) ∂timeMeasure T
  have hX : MemLp X 2 μ := (Lp.memLp (J.integral (stop F μ T c R))).sub
    (Lp.memLp (J.integral (stop F μ T a R)))
  have hY : MemLp Y 2 μ := (Lp.memLp ((I).integral (stop F μ T c u))).sub
    (Lp.memLp ((I).integral (stop F μ T a u)))
  have hXY : Integrable (fun ω => X ω • Y ω) μ := memLp_one_iff_integrable.mp (hX.smul hY)
  have hQ : Integrable Q μ := interval_integrable F μ T a c u
  have hz : (fun ω => μ[(fun ω => X ω • Y ω) | F a] ω - μ[Q | F a] ω) =ᵐ[μ] (fun _ => (0:E)) := by
    apply ae_eq_zero_of_forall_inner (𝕜 := ℝ)
    intro q
    have hc := HeatHilbertIntervalExact.conditional_cross_interval I
      (HeatTerminalNaturality.locality F μ T b J hlocal) hac
      (RotatedCylindricalCoordinates.constant F μ T q) u
    have hleft : (fun ω => inner ℝ
        ((I).integral (stop F μ T c (RotatedCylindricalCoordinates.constant F μ T q)) ω -
          (I).integral (stop F μ T a (RotatedCylindricalCoordinates.constant F μ T q)) ω)
        (Y ω)) =ᵐ[μ] (fun ω => inner ℝ q (X ω • Y ω)) := by
      filter_upwards [HeatTerminalBrownian.constant_integral F μ T b J q c,
        HeatTerminalBrownian.constant_integral F μ T b J q a] with ω hc ha
      rw [hc,ha,← sub_smul]
      simp only [real_inner_smul_left,real_inner_smul_right]
      rfl
    have hl := condExp_congr_ae (m := F a) hleft
    have hr := condExp_congr_ae (m := F a) (bracket_pairing F μ T q a c u)
    have hp := (hl.symm.trans hc).trans hr
    have h1 := (innerSL ℝ q).comp_condExp_comm (m := F a) hXY
    have h2 := (innerSL ℝ q).comp_condExp_comm (m := F a) hQ
    filter_upwards [h1,h2,hp] with ω h1 h2 hp
    change inner ℝ q (_ - _) = 0
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (h1.trans (hp.trans h2.symm))
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

end HeatVectorConditionalCross
#check @HeatVectorConditionalCross.process_integrable
#print axioms HeatVectorConditionalCross.process_integrable
#check @HeatVectorConditionalCross.interval_integrable
#print axioms HeatVectorConditionalCross.interval_integrable
#check @HeatVectorConditionalCross.bracket_pairing
#print axioms HeatVectorConditionalCross.bracket_pairing
#check @HeatVectorConditionalCross.conditional_cross
#print axioms HeatVectorConditionalCross.conditional_cross
