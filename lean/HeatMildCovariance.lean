import HeatMildBrownianMoment
import HeatConditionalFubini

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatMildCovariance
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open HeatMildSolution HeatPredictableStateInput
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

def kernel (a b : ℝ≥0) (z : Ω → E) (p : ℝ≥0 × Ω) : E :=
  S (b-p.1) (M (S (p.1-a) (z p.2)))

include hS hcontr in
theorem kernel_measurable (a b : ℝ≥0) (z : Ω → E) (hz : Measurable z) :
    Measurable (kernel S M a b z) := by
  have hact := (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable
  have hz' := hact.comp ((measurable_fst.sub_const a).prodMk (hz.comp measurable_snd))
  exact hact.comp ((measurable_const.sub measurable_fst).prodMk (M.continuous.measurable.comp hz'))

include hcontr in
theorem kernel_bound (a b : ℝ≥0) (z : Ω → E) (p : ℝ≥0 × Ω) :
    ‖kernel S M a b z p‖ ≤ ‖M‖ * ‖z p.2‖ := by
  exact (hcontr _ _).trans ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hcontr _ _) (norm_nonneg _)))

include hS hcontr in
theorem kernel_integrable (ν : Measure ℝ≥0) [IsFiniteMeasure ν] (μ : Measure Ω) [IsFiniteMeasure μ]
    (a b : ℝ≥0) (z : Ω → E) (hz : Measurable z) (hzm : MemLp z 2 μ) :
    Integrable (kernel S M a b z) (ν.prod μ) := by
  have hbound := (hzm.norm.const_mul ‖M‖).comp_snd ν
  have hk : MemLp (kernel S M a b z) 2 (ν.prod μ) := by
    apply hbound.mono' (kernel_measurable S hS hcontr M a b z hz).aestronglyMeasurable
    exact Eventually.of_forall (kernel_bound S hcontr M a b z)
  exact hk.integrable one_le_two

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  {κ : Type*} [Countable κ] (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance

include hS hcontr hsem in
theorem conditional_bracket (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0}
    (g : E) (u : Process (E := E) F μ H)
    (hu : u = HeatVolterraForcing.orbit F μ H S hS hcontr g +
      HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u) :
    μ[(fun ω => ∫ s in Set.Ioc a b, S (b-s) (M (u (s,ω))) ∂timeMeasure H) | F a] =ᵐ[μ]
      (fun ω => ∫ s in Set.Ioc a b, kernel S M a b
        (value F μ H S hS hcontr M I g u a) (s,ω) ∂timeMeasure H) := by
  let ν := (timeMeasure H).restrict (Set.Ioc a b)
  let Va := value F μ H S hS hcontr M I g u a
  obtain ⟨Z,hZ,hrep⟩ := value_adapted F μ H S hS hcontr M I g u a
  have hZm : MemLp Z 2 μ := (Lp.memLp Va).ae_eq hrep
  have hfi0 : Integrable (fun p : ℝ≥0 × Ω => S (b-p.1) (M (u p))) (energyMeasure μ H) :=
    (HeatVectorConditionalCross.process_integrable F μ H (factor F μ H S hS hcontr M b u)).congr
      (factor_ae F μ H S hS hcontr M b u)
  have hfi : Integrable (fun p : ℝ≥0 × Ω => S (b-p.1) (M (u p))) (ν.prod μ) :=
    hfi0.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hgi := kernel_integrable S hS hcontr M ν μ a b Z (hZ.mono (F.le a)).measurable hZm
  have hG : AEStronglyMeasurable[F a] (fun ω => ∫ s, kernel S M a b Z (s,ω) ∂ν) μ := by
    have hGsm : StronglyMeasurable[F a] (fun ω => ∫ s, kernel S M a b Z (s,ω) ∂ν) := by
      letI : MeasurableSpace Ω := F a
      exact StronglyMeasurable.integral_prod_left (μ := ν)
        (f := fun s ω => kernel S M a b Z (s,ω))
        (kernel_measurable S hS hcontr M a b Z hZ.measurable).stronglyMeasurable
    exact hGsm.aestronglyMeasurable
  have hus := value_slices F μ H S hS hcontr M I hsem g u hu
  have hfg : ∀ᵐ s ∂ν, μ[(fun ω => S (b-s) (M (u (s,ω)))) | F a] =ᵐ[μ]
      (fun ω => kernel S M a b Z (s,ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hus] with s hs hsrep
    let L := (S (b-s)).comp M
    have huI : MemLp (fun ω => u (s,ω)) 2 μ :=
      (Lp.memLp (value F μ H S hS hcontr M I g u s)).ae_eq hsrep.symm
    have hcomm := L.comp_condExp_comm (m := F a) (huI.integrable one_le_two)
    have hmean := (condExp_congr_ae (m := F a) hsrep).trans
      (HeatMildRestart.conditional_mean F μ H S hS hcontr M hsem basis J hlocal hs.1.le g u)
    filter_upwards [hcomm,hmean,hrep] with ω hc hm hz
    change L (μ[(fun ω => u (s,ω)) | F a] ω) = μ[(fun ω => L (u (s,ω))) | F a] ω at hc
    change μ[(fun ω => L (u (s,ω))) | F a] ω = _
    rw [← hc,hm,hz]
    rfl
  have ht := HeatConditionalFubini.conditional_integral ν μ F a
    (fun p : ℝ≥0 × Ω => S (b-p.1) (M (u p))) (kernel S M a b Z) hfi hgi hG hfg
  have he : (fun ω => ∫ s, kernel S M a b Z (s,ω) ∂ν) =ᵐ[μ]
      (fun ω => ∫ s, kernel S M a b Va (s,ω) ∂ν) := by
    filter_upwards [hrep] with ω hω
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => congrArg (fun z => S (b-s) (M (S (s-a) z))) hω.symm)
  exact ht.trans he

end HeatMildCovariance
#check @HeatMildCovariance.kernel_measurable
#print axioms HeatMildCovariance.kernel_measurable
#check @HeatMildCovariance.kernel_bound
#print axioms HeatMildCovariance.kernel_bound
#check @HeatMildCovariance.kernel_integrable
#print axioms HeatMildCovariance.kernel_integrable
#check @HeatMildCovariance.conditional_bracket
#print axioms HeatMildCovariance.conditional_bracket
