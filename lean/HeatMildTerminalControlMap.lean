import HeatPredictableControlConvolution
import HeatMildSolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatMildTerminalControlMap

open Filter MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s + t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)
  (hn : NullCompleteFiltration.ContainsNullSets F μ)

local notation "Proc" => Process (E := E) F μ H
local notation "orbit" => HeatVolterraSolutionLinear.orbit F μ H S hS hcontr
local notation "det" => HeatPredictableControlConvolution.convolution F μ H S hS hcontr hn
local notation "atDet" => HeatPredictableControlConvolution.atTime F μ H S hS hcontr
local notation "sl" => HeatVolterraSolutionLinear.sliceOperator F μ H S hS hcontr M
local notation "N" => HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I

/-- The actual predictable fixed point, linearly in the initial state
and the predictable forcing. -/
def process : E × Proc →L[ℝ] Proc :=
  (HeatVolterraSolutionLinear.solve F μ H S hS hcontr M hsem I).comp
    ((orbit).comp (ContinuousLinearMap.fst ℝ E Proc) +
      (det).comp (ContinuousLinearMap.snd ℝ E Proc))

local notation "V" => process F μ H S hS hcontr M hsem I hn

/-- At each deterministic time, the actual mild state is a continuous
linear function of the initial state and predictable forcing. -/
def atTime (t : ℝ≥0) : E × Proc →L[ℝ] Lp E 2 μ :=
  ((Lp.constL 2 μ ℝ).comp (S t)).comp (ContinuousLinearMap.fst ℝ E Proc) +
    (atDet t).comp (ContinuousLinearMap.snd ℝ E Proc) +
    I.integral.toContinuousLinearMap.comp ((sl t).comp V)

local notation "X" => atTime F μ H S hS hcontr M hsem I hn

include hS hcontr in
theorem process_equation (g : E) (f : Proc) :
    V (g, f) = orbit g + det f + N (V (g, f)) :=
  HeatVolterraSolutionLinear.solve_equation F μ H S hS hcontr M hsem I (orbit g + det f)

include hS hcontr in
theorem atTime_eq (g : E) (f : Proc) (t : ℝ≥0) :
    X t (g, f) = Lp.const 2 μ (S t g) + atDet t f +
      I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t (V (g, f))) := rfl

include hS hcontr in
theorem atTime_ae (g : E) (f : Proc) (t : ℝ≥0) :
    (X t (g, f) : Ω → E) =ᵐ[μ] fun ω => S t g + HeatControlConvolution.value H S f t ω +
      I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t (V (g, f))) ω := by
  rw [atTime_eq]
  filter_upwards [Lp.coeFn_const 2 μ (S t g),
    HeatPredictableControlConvolution.atTime_ae F μ H S hS hcontr t f,
    Lp.coeFn_add (Lp.const 2 μ (S t g)) (atDet t f),
    Lp.coeFn_add (Lp.const 2 μ (S t g) + atDet t f)
      (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t (V (g, f))))]
    with ω hc hf hd hn
  rw [hn, Pi.add_apply, hd, Pi.add_apply, hc, hf]
  rfl

include hS hcontr in
theorem initial_value (hzero : S 0 = ContinuousLinearMap.id ℝ E) (g : E) (f : Proc) :
    X 0 (g, f) = Lp.const 2 μ g := by
  rw [atTime_eq, HeatPredictableControlConvolution.atTime_zero, add_zero,
    HeatMildSolution.slice_zero, map_zero, add_zero, hzero]
  rfl

include hS hcontr in
theorem state_slices (g : E) (f : Proc) :
    ∀ᵐ t ∂timeMeasure H, (fun ω => V (g, f) (t, ω)) =ᵐ[μ] X t (g, f) := by
  let u := V (g, f)
  let w := orbit g
  let v := det f
  have hsum : (u : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H]
      fun p => w p + v p + N u p := by
    have h₁ := ae_eq_of_ae_eq_trim (Lp.coeFn_add (w + v) (N u))
    have h₂ := ae_eq_of_ae_eq_trim (Lp.coeFn_add w v)
    have hu : u = w + v + N u := process_equation F μ H S hS hcontr M hsem I hn g f
    rw [← hu] at h₁
    filter_upwards [h₁, h₂] with p h₁ h₂
    exact h₁.trans (congrArg (fun z : E => z + N u p) h₂)
  filter_upwards [Measure.ae_ae_of_ae_prod hsum,
    Measure.ae_ae_of_ae_prod (HeatVolterraForcing.orbit_ae F μ H S hS hcontr g),
    HeatPredictableControlConvolution.convolution_slices F μ H S hS hcontr hn f,
    HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u] with t hsum hw hv hz
  filter_upwards [hsum, hw, hv, hz, atTime_ae F μ H S hS hcontr M hsem I hn g f t,
    HeatPredictableControlConvolution.atTime_ae F μ H S hS hcontr t f]
    with ω hsum hw hv hz hx hdet
  change u (t, ω) = X t (g, f) ω
  change v (t, ω) = _ at hv
  change w (t, ω) = _ at hw
  change N u (t, ω) = _ at hz
  rw [hsum, hw, hv, hz, hdet, hx]

include hS hcontr in
theorem state_regular [Nontrivial E] (g : E) (f : Proc) :
    Continuous (fun t => X t (g, f)) ∧
      ∀ t, ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ (X t (g, f) : Ω → E) =ᵐ[μ] Z := by
  obtain ⟨hD, hDa⟩ := HeatPredictableControlConvolution.atTime_regular F μ H S hS hcontr hn f
  let u := V (g, f)
  let Y := HeatMildSolution.value F μ H S hS hcontr M I g u
  have he (t : ℝ≥0) : X t (g, f) = Y t + atDet t f := by
    rw [atTime_eq]
    change _ = (Lp.const 2 μ (S t g) +
      I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)) + atDet t f
    abel
  refine ⟨?_, fun t => ?_⟩
  · simp_rw [he]
    exact (HeatMildSolution.value_continuous F μ H S hS hcontr M I g u).add hD
  · obtain ⟨Z, hZm, hZ⟩ := HeatMildSolution.value_adapted F μ H S hS hcontr M I g u t
    obtain ⟨W, hWm, hW⟩ := hDa t
    refine ⟨fun ω => Z ω + W ω, hZm.add hWm, ?_⟩
    rw [he]
    filter_upwards [Lp.coeFn_add (Y t) (atDet t f), hZ, hW] with ω h hZ hW
    rw [h, Pi.add_apply, hZ, hW]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The terminal operator for local controls with a prescribed spatial
injection, starting from zero. -/
def terminalControl (B : U →L[ℝ] E) : Process (E := U) F μ H →L[ℝ] Lp E 2 μ :=
  (X H).comp ((ContinuousLinearMap.inr ℝ E Proc).comp (HeatPredictableObservation.lift F μ H B))

include hS hcontr in
theorem terminal_split (B : U →L[ℝ] E) (g : E) (u : Process (E := U) F μ H) :
    X H (g, HeatPredictableObservation.lift F μ H B u) =
      X H (g, 0) + terminalControl F μ H S hS hcontr M hsem I hn B u := by
  change X H (g, HeatPredictableObservation.lift F μ H B u) =
    X H (g, 0) + X H (0, HeatPredictableObservation.lift F μ H B u)
  rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]

end HeatMildTerminalControlMap

#print axioms HeatMildTerminalControlMap.process_equation
#print axioms HeatMildTerminalControlMap.atTime_ae
#print axioms HeatMildTerminalControlMap.state_slices
#print axioms HeatMildTerminalControlMap.state_regular
#print axioms HeatMildTerminalControlMap.terminal_split
