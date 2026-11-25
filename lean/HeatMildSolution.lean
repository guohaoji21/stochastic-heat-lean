import HeatVolterraContinuity
import HeatVolterraFixedPoint
import HeatVolterraForcing

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatMildSolution
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatVolterraSlice
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

local instance : Fact ((1:ENNReal) ≤ 2) := ⟨by norm_num⟩

def value (g : E) (u : Process (E := E) F μ H) (t : ℝ≥0) : Lp E 2 μ :=
  Lp.const 2 μ (S t g) + I.integral (slice F μ H S hS hcontr M t u)

theorem value_continuous (g : E) (u : Process (E := E) F μ H) :
    Continuous (value F μ H S hS hcontr M I g u) := by
  exact ((Lp.constL 2 μ ℝ).continuous.comp (hS g)).add
    (HeatVolterraContinuity.integral_continuous F μ H S hS hcontr M I u)

theorem value_adapted (g : E) (u : Process (E := E) F μ H) (t : ℝ≥0) :
    ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ value F μ H S hS hcontr M I g u t =ᵐ[μ] Z := by
  obtain ⟨Z,hZ,hrep⟩ := I.adapted t (slice F μ H S hS hcontr M t u)
    (StoppedItoInputs.stop_stopped F μ H t _)
  refine ⟨fun ω => S t g + Z ω, stronglyMeasurable_const.add hZ, ?_⟩
  filter_upwards [Lp.coeFn_add (Lp.const 2 μ (S t g))
    (I.integral (slice F μ H S hS hcontr M t u)), Lp.coeFn_const 2 μ (S t g), hrep] with ω ha hc hi
  change (Lp.const 2 μ (S t g) + I.integral (slice F μ H S hS hcontr M t u)) ω = _
  rw [ha]
  simp only [Pi.add_apply,hc,hi,Function.const_apply]

theorem slice_zero (u : Process (E := E) F μ H) : slice F μ H S hS hcontr M 0 u = 0 := by
  apply SHE.PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [slice_ae F μ H S hS hcontr M 0 u, ae_eq_of_ae_eq_trim (Lp.coeFn_zero E 2 _)] with p hp hz
  rw [hp,hz]
  simp only [HeatVolterraKernel.raw, not_lt_zero, ite_false,Pi.zero_apply]

theorem initial_value (hzero : S 0 = ContinuousLinearMap.id ℝ E) (g : E)
    (u : Process (E := E) F μ H) : value F μ H S hS hcontr M I g u 0 = Lp.const 2 μ g := by
  unfold value
  rw [slice_zero F μ H S hS hcontr M u, map_zero, add_zero, hzero]
  rfl

theorem value_slices (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    (g : E) (u : Process (E := E) F μ H)
    (hu : u = HeatVolterraForcing.orbit F μ H S hS hcontr g +
      HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u) :
    ∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω)) =ᵐ[μ] value F μ H S hS hcontr M I g u t := by
  have hf := Measure.ae_ae_of_ae_prod (HeatVolterraForcing.orbit_ae F μ H S hS hcontr g)
  have hc := HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u
  have ha : ∀ᵐ t ∂timeMeasure H, ∀ᵐ ω ∂μ,
      u (t,ω) = HeatVolterraForcing.orbit F μ H S hS hcontr g (t,ω) +
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω) := by
    have hh := ae_eq_of_ae_eq_trim (Lp.coeFn_add (HeatVolterraForcing.orbit F μ H S hS hcontr g)
      (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u))
    rw [← hu] at hh
    exact Measure.ae_ae_of_ae_prod hh
  filter_upwards [hf,hc,ha] with t ht hc ha
  filter_upwards [ht,hc,ha,Lp.coeFn_add (Lp.const 2 μ (S t g))
    (I.integral (slice F μ H S hS hcontr M t u)),Lp.coeFn_const 2 μ (S t g)] with ω hf hc ha hs hk
  change u (t,ω) = (Lp.const 2 μ (S t g) + I.integral (slice F μ H S hS hcontr M t u)) ω
  rw [hs]
  simp only [Pi.add_apply,hk,Function.const_apply]
  rw [ha,hf]
  exact congrArg (fun z : E => S t g + z) hc

theorem exists_unique_mild (hsem : ∀ s t, S (s+t) = (S s).comp (S t)) (g : E) :
    ∃! u : Process (E := E) F μ H,
      u = HeatVolterraForcing.orbit F μ H S hS hcontr g +
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      Continuous (value F μ H S hS hcontr M I g u) ∧
      (∀ t, ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ value F μ H S hS hcontr M I g u t =ᵐ[μ] Z) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω)) =ᵐ[μ] value F μ H S hS hcontr M I g u t) := by
  obtain ⟨u,hu,hunique⟩ := HeatVolterraFixedPoint.exists_unique F μ H S hS hcontr M hsem I
    (HeatVolterraForcing.orbit F μ H S hS hcontr g)
  refine ⟨u, ⟨hu, value_continuous F μ H S hS hcontr M I g u,
    value_adapted F μ H S hS hcontr M I g u, value_slices F μ H S hS hcontr M I hsem g u hu⟩, ?_⟩
  intro v hv
  exact hunique v hv.1

end HeatMildSolution
#check @HeatMildSolution.value_continuous
#print axioms HeatMildSolution.value_continuous
#check @HeatMildSolution.value_adapted
#print axioms HeatMildSolution.value_adapted
#check @HeatMildSolution.slice_zero
#print axioms HeatMildSolution.slice_zero
#check @HeatMildSolution.initial_value
#print axioms HeatMildSolution.initial_value
#check @HeatMildSolution.value_slices
#print axioms HeatMildSolution.value_slices
#check @HeatMildSolution.exists_unique_mild
#print axioms HeatMildSolution.exists_unique_mild
