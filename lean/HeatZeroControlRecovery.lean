import HeatVariationalProperties
import HeatMildSecondMoment

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatZeroControlRecovery
open MeasureTheory Filter SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (I : SHE.StandardTerminalIto (C := Base) (E := Base) F μ H)
  (hU : IsStronglyProgressive F (fun (_ : ℝ≥0) (_ : Ω) => (0:Base)))
  (hE : Integrable (fun _p : ℝ≥0 × Ω => ‖(0:Base)‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M I (fun _ _ => 0) hU hE g)

theorem control_zero (t : ℝ≥0) (ω : Ω) :
    HeatControlConvolution.value H family (HeatControlAdapted.clamp (fun (_ : ℝ≥0) (_ : Ω) => (0:Base)) H) t ω=0 := by
  simp [HeatControlConvolution.value,HeatControlConvolution.raw,HeatVolterraKernel.raw,HeatControlAdapted.clamp]

theorem value_eq (t : ℝ≥0) : sol.value t=
    HeatMildSolution.value F μ H family family_continuous family_contraction M I g sol.input t := by
  apply Lp.ext
  filter_upwards [sol.mild_equation t,
    Lp.coeFn_add (Lp.const 2 μ (family t g))
      (I.integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t sol.input)),
    Lp.coeFn_const 2 μ (family t g)] with ω hr ha hc
  simp only [control_zero H,add_zero] at hr
  change sol.value t ω=(Lp.const 2 μ (family t g)+I.integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t sol.input)) ω
  rw [ha]
  simp only [Pi.add_apply,hc,Function.const_apply]
  exact hr

theorem fixed_point : sol.input=HeatVolterraForcing.orbit F μ H family family_continuous family_contraction g+
    HeatVolterraFixedPoint.convolution F μ H family family_continuous family_contraction M family_semigroup I sol.input := by
  let A := HeatVolterraForcing.orbit F μ H family family_continuous family_contraction g+sol.forcing
  have ha := HeatForcingIdentification.forcing_ae F μ H family family_continuous family_contraction M family_semigroup I
    A sol.input sol.fixed_point sol.value sol.input_slices (fun t _ => family t g)
    ((family_continuous g).measurable.comp measurable_fst) (by
      intro t
      simpa only [control_zero H,add_zero] using sol.mild_equation t)
  have he : A=HeatVolterraForcing.orbit F μ H family family_continuous family_contraction g :=
    SHE.PastItoAlgebra.eq_of_ambient_ae F μ H (ha.trans (HeatVolterraForcing.orbit_ae F μ H family family_continuous family_contraction g).symm)
  calc
    _ = A+HeatVolterraFixedPoint.convolution F μ H family family_continuous family_contraction M family_semigroup I sol.input := sol.fixed_point
    _ = _ := congrArg (fun x => x+HeatVolterraFixedPoint.convolution F μ H family family_continuous family_contraction M family_semigroup I sol.input) he

end HeatZeroControlRecovery
#check @HeatZeroControlRecovery.control_zero
#print axioms HeatZeroControlRecovery.control_zero
#check @HeatZeroControlRecovery.value_eq
#print axioms HeatZeroControlRecovery.value_eq
#check @HeatZeroControlRecovery.fixed_point
#print HeatZeroControlRecovery.fixed_point
#print axioms HeatZeroControlRecovery.fixed_point
