import HeatMildTerminalControlMap
import HeatTorusControlObservation
import HeatTorusUniformControlled
import HeatCanonicalSeparable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace HeatTorusMildTerminalControl

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns UnitAddTorus
open HeatTorusProjectedConvolution (fullHeat fullHeat_continuous fullHeat_contraction)
open HeatTorusControlObservation (Control restriction extension)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology

local notation "Ω" => C(ℝ≥0, ℝ)
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

def indices (ι : Type*) [Fintype ι] : Set (HeatTorusFourier.State ι) :=
  Classical.choose (HeatCountableBasis.exists_countable_hilbertBasis (E := HeatTorusFourier.State ι))

instance (ι : Type*) [Fintype ι] : Countable (indices ι) :=
  (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis
    (E := HeatTorusFourier.State ι))).1.to_subtype

def basis (ι : Type*) [Fintype ι] : HilbertBasis (indices ι) ℝ (HeatTorusFourier.State ι) :=
  Classical.choice (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis
    (E := HeatTorusFourier.State ι))).2

theorem heat_add (P : ℝ) (s t : ℝ≥0) :
    fullHeat (ι := ι) P (s + t) = (fullHeat P s).comp (fullHeat P t) := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun (op : Full →L[ℂ] Full) => op x)
    (HeatTorusFourier.heat_add (ι := ι) P s.property t.property)

theorem heat_zero (P : ℝ) : fullHeat (ι := ι) P 0 = ContinuousLinearMap.id ℝ Full := by
  apply ContinuousLinearMap.ext
  intro x
  change HeatTorusFourier.heat P 0 x = x
  rw [HeatTorusFourier.heat_zero]
  rfl

def ito (ι : Type*) [Fintype ι] (H : ℝ≥0) :
    StandardTerminalIto (C := HeatTorusFourier.State ι) (E := HeatTorusFourier.State ι) F μ H :=
  HeatTerminalNaturality.integral F μ H (basis ι) (HeatCanonicalNative.scalar H)

variable (P : ℝ) (b : C(UnitAddTorus ι, ℂ)) (O : Set (UnitAddTorus ι)) (H : ℝ≥0)

local notation "M" => HeatTorusGalerkinCompression.fullMultiplier b
local notation "hn" => HeatCanonicalNullComplete.contains_nulls
local notation "A" => HeatMildTerminalControlMap.atTime F μ H (fullHeat P) (fullHeat_continuous P)
  (fullHeat_contraction P) M (heat_add P) (ito ι H) hn

def injection (O : Set (UnitAddTorus ι)) : Control O →L[ℝ] Full :=
  (extension O).restrictScalars ℝ

def input : Process (E := Control O) F μ H →L[ℝ] Process (E := Full) F μ H :=
  HeatPredictableObservation.lift F μ H (injection O)

def process (g : Full) (u : Process (E := Control O) F μ H) : Process (E := Full) F μ H :=
  HeatMildTerminalControlMap.process F μ H (fullHeat P) (fullHeat_continuous P)
    (fullHeat_contraction P) M (heat_add P) (ito ι H) hn (g, input O H u)

def state (g : Full) (u : Process (E := Control O) F μ H) (t : ℝ≥0) : Lp Full 2 μ :=
  A t (g, input O H u)

/-- The full torus terminal control operator for predictable local controls
with zero initial value. -/
def terminalControl : Process (E := Control O) F μ H →L[ℝ] Lp Full 2 μ :=
  HeatMildTerminalControlMap.terminalControl F μ H (fullHeat P) (fullHeat_continuous P)
    (fullHeat_contraction P) M (heat_add P) (ito ι H) hn (injection O)

theorem terminal_split (g : Full) (u : Process (E := Control O) F μ H) :
    state P b O H g u H = state P b O H g 0 H + terminalControl P b O H u := by
  have h := HeatMildTerminalControlMap.terminal_split F μ H (fullHeat P) (fullHeat_continuous P)
    (fullHeat_contraction P) M (heat_add P) (ito ι H) hn (injection O) g u
  change state P b O H g u H = A H (g, 0) + terminalControl P b O H u at h
  simpa only [state, map_zero] using h

theorem state_properties (g : Full) (u : Process (E := Control O) F μ H) :
    Continuous (state P b O H g u) ∧
      state P b O H g u 0 = Lp.const 2 μ g ∧
      (∀ t, ∃ Z : Ω → Full, StronglyMeasurable[F t] Z ∧ state P b O H g u t =ᵐ[μ] Z) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => process P b O H g u (t, ω)) =ᵐ[μ] state P b O H g u t) ∧
      (∀ t, state P b O H g u t =ᵐ[μ] fun ω => fullHeat P t g +
        HeatControlConvolution.value H (fullHeat P) (input O H u) t ω +
        (ito ι H).integral
          (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P)
            M t (process P b O H g u)) ω) := by
  let x : Full := mFourierBasis (d := ι) (0 : ι → ℤ)
  have hx : ‖x‖ = 1 := (mFourierBasis (d := ι)).orthonormal.norm_eq_one _
  let : Nontrivial Full := ⟨⟨x, 0, fun he => by rw [he, norm_zero] at hx; exact zero_ne_one hx⟩⟩
  obtain ⟨hc, ha⟩ := HeatMildTerminalControlMap.state_regular F μ H (fullHeat P) (fullHeat_continuous P)
    (fullHeat_contraction P) M (heat_add P) (ito ι H) hn g (input O H u)
  refine ⟨hc, ?_, ha, ?_, fun t => ?_⟩
  · exact HeatMildTerminalControlMap.initial_value F μ H (fullHeat P) (fullHeat_continuous P)
      (fullHeat_contraction P) M (heat_add P) (ito ι H) hn (heat_zero P) g (input O H u)
  · exact HeatMildTerminalControlMap.state_slices F μ H (fullHeat P) (fullHeat_continuous P)
      (fullHeat_contraction P) M (heat_add P) (ito ι H) hn g (input O H u)
  · exact HeatMildTerminalControlMap.atTime_ae F μ H (fullHeat P) (fullHeat_continuous P)
      (fullHeat_contraction P) M (heat_add P) (ito ι H) hn g (input O H u) t

/-- The linear full-space trajectory satisfies the same uniform
high-frequency estimate, for its actual predictable injected control. -/
theorem tail_le (hP : 0 < P) (g : Full) (u : Process (E := Control O) F μ H) (n : ℕ) :
    HeatForwardTailEnergy.trajectoryEnergy μ H (HeatTorusUniformTail.tail (ι := ι) n)
      (state P b O H g u) ≤
        3 * HeatRegularKernel.mass (HeatTorusUniformTail.rate P n) *
          HeatForwardTailEnergy.energyBound H M g (‖u‖ ^ 2) := by
  let f := input O H u
  let v := HeatPredictableControlConvolution.convolution F μ H (fullHeat P) (fullHeat_continuous P)
    (fullHeat_contraction P) hn f
  have hfix : process P b O H g u =
      HeatVolterraForcing.orbit F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P) g + v +
        HeatVolterraFixedPoint.convolution F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P)
          M (heat_add P) (ito ι H) (process P b O H g u) :=
    HeatMildTerminalControlMap.process_equation F μ H (fullHeat P) (fullHeat_continuous P)
      (fullHeat_contraction P) M (heat_add P) (ito ι H) hn g f
  have hv : ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] HeatControlConvolution.value H (fullHeat P) f t := by
    filter_upwards [HeatPredictableControlConvolution.convolution_slices F μ H (fullHeat P)
      (fullHeat_continuous P) (fullHeat_contraction P) hn f] with t ht
    exact ht.trans (HeatPredictableControlConvolution.atTime_ae F μ H (fullHeat P)
      (fullHeat_continuous P) (fullHeat_contraction P) t f)
  have h := HeatForwardTailEnergy.bound F μ H (fullHeat P) (fullHeat_continuous P)
    (fullHeat_contraction P) M (HeatTorusUniformTail.tail (ι := ι) n)
    (heat_add P) (basis ι) (HeatCanonicalNative.scalar H) (HeatTorusUniformTail.rate_pos hP n)
    (HeatTorusUniformTail.heat_decay P n) g f
    (HeatPredictableObservation.measurable_process F μ H f)
    (HeatPredictableObservation.ambient_memLp F μ H f) v (process P b O H g u) hfix hv
    (state P b O H g u) (state_properties P b O H g u).2.2.2.1
  have he : HeatForwardTailEnergy.controlEnergy μ H f = ‖f‖ ^ 2 :=
    (subsigma_norm_sq (energyMeasure μ H) (predictable_le_product F) f).symm
  have hc : ‖f‖ ≤ ‖u‖ := by
    let : MeasurableSpace (ℝ≥0 × Ω) := HeatCanonicalUsual56.usualFiltration.predictable
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(injection O).coeFn_compLpL u] with p hp
    change f p = injection O (u p) at hp
    rw [hp]
    have hr : ‖restriction O‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      rw [one_mul]
      exact norm_Lp_toLp_restrict_le O x
    have hq : ‖extension O‖ ≤ 1 := by
      change ‖(restriction O).adjoint‖ ≤ 1
      rw [LinearIsometryEquiv.norm_map]
      exact hr
    have hle := mul_le_mul_of_nonneg_right hq (norm_nonneg (u p))
    rw [one_mul] at hle
    exact ((extension O).le_opNorm _).trans hle
  rw [he] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num)
    (HeatRegularKernel.mass_nonneg _ (HeatTorusUniformTail.rate_pos hP n))))
  unfold HeatForwardTailEnergy.energyBound
  have hs := pow_le_pow_left₀ (norm_nonneg _) hc 2
  gcongr

end HeatTorusMildTerminalControl

#print axioms HeatTorusMildTerminalControl.terminal_split
#print axioms HeatTorusMildTerminalControl.state_properties
#print axioms HeatTorusMildTerminalControl.tail_le
