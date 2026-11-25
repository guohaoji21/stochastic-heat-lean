import HeatVolterraSlice
import SHE.ProductLpIdentification
import SHE.KernelItoLimit
import SHE.LeftFrozenFiniteHaarCells

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatVolterraContinuity
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatVolterraKernel HeatVolterraSlice
open scoped NNReal ENNReal Topology

section Slices
variable {X Ω E : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (ν : Measure X) (μ : Measure Ω) [SFinite ν] [IsFiniteMeasure μ]

theorem ae_slices_of_slice_limits (v : ℕ → Lp E 2 (ν.prod μ)) (V : Lp E 2 (ν.prod μ))
    (hv : Tendsto v atTop (𝓝 V)) (W : X → Lp E 2 μ)
    (hs : ∀ᵐ t ∂ν, TendstoInMeasure μ (fun n ω => v n (t,ω)) atTop (W t)) :
    ∀ᵐ t ∂ν, (fun ω => V (t,ω)) =ᵐ[μ] W t := by
  obtain ⟨ns,hns,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hAE,hs] with t ht hslice
  have hm (n : ℕ) : AEStronglyMeasurable (fun ω => v (ns n) (t,ω)) μ :=
    ((Lp.stronglyMeasurable (v (ns n))).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae hm ht)
    (hslice.comp hns.tendsto_atTop)
end Slices

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
include hS hcontr
local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance

theorem slice_continuous (u : Process (E := E) F μ H) :
    Continuous (fun t => slice F μ H S hS hcontr M t u) := by
  apply continuous_iff_seqContinuous.mpr
  intro a t ha
  let A := ambientIsometry (E := E) (energyMeasure μ H) (predictable_le_product F)
  let v : ℕ → Lp E 2 (energyMeasure μ H) := fun n => A (slice F μ H S hS hcontr M (a n) u)
  let f : Lp E 2 (energyMeasure μ H) := A (slice F μ H S hS hcontr M t u)
  let g : Lp E 2 (energyMeasure μ H) := ‖M‖ • A u
  have hV : ∀ n, (v n : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] (fun p => raw S M u (a n,p)) :=
    fun n => (ambient_ae _ _ _).trans (slice_ae F μ H S hS hcontr M (a n) u)
  have hf : (f : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] (fun p => raw S M u (t,p)) :=
    (ambient_ae _ _ _).trans (slice_ae F μ H S hS hcontr M t u)
  have hg : (g : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] (fun p => ‖M‖ • u p) := by
    filter_upwards [Lp.coeFn_smul ‖M‖ (A u), ambient_ae _ _ u] with p hs hu
    rw [hs]
    change ‖M‖ • (A u p) = ‖M‖ • u p
    exact congrArg (fun z : E => ‖M‖ • z) hu
  have hvlim : Tendsto v atTop (𝓝 f) := by
    apply dominated_Lp_convergence _ v f g
    · intro n
      filter_upwards [hV n,hg] with p hn hgg
      rw [hn,hgg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg M)]
      exact HeatVolterraModel.raw_norm_bound F μ H S hS hcontr M u (a n,p)
    · have hn : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 ≠ t :=
        Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne t)
      filter_upwards [ae_all_iff.mpr hV,hf,hn] with p hp hpf hne
      have hl := raw_sequence_tendsto S hS hcontr M u a t ha p.1 p.2 hne
      simpa only [← hp, ← hpf] using hl
  exact A.isometry.tendsto_nhds_iff.mpr hvlim

variable (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem integral_continuous (u : Process (E := E) F μ H) :
    Continuous (fun t => I.integral (slice F μ H S hS hcontr M t u)) :=
  I.integral.continuous.comp (slice_continuous F μ H S hS hcontr M u)

theorem convolution_slices (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    (u : Process (E := E) F μ H) :
    ∀ᵐ t ∂timeMeasure H,
      (fun ω => SHE.KernelItoLimit.convolution (HeatVolterraModel.model F μ H S hS hcontr M hsem) I u (t,ω))
        =ᵐ[μ] I.integral (slice F μ H S hS hcontr M t u) := by
  let K := HeatVolterraModel.model F μ H S hS hcontr M hsem
  let A := ambientIsometry (E := E) (energyMeasure μ H) (predictable_le_product F)
  let v : ℕ → Lp E 2 (energyMeasure μ H) := fun n => A (SHE.KernelItoLimit.output K I u n)
  let V : Lp E 2 (energyMeasure μ H) := A (SHE.KernelItoLimit.convolution K I u)
  have hv : Tendsto v atTop (𝓝 V) :=
    A.continuous.continuousAt.tendsto.comp (SHE.KernelItoLimit.approximation_tendsto K I u)
  have hApprox : ∀ n, ∀ᵐ t ∂timeMeasure H,
      (fun ω => v n (t,ω)) =ᵐ[μ] I.integral (K.input u n (SHE.ApproximationCells.index n t)) := by
    intro n
    have h1 : ∀ᵐ t ∂timeMeasure H, (fun ω => v n (t,ω)) =ᵐ[μ]
        (fun ω => SHE.KernelItoLimit.output K I u n (t,ω)) :=
      Measure.ae_ae_of_ae_prod (ambient_ae _ _ (SHE.KernelItoLimit.output K I u n))
    have h2 := SHE.PredictableItoCells.output_slice_ae I n (K.input u n) (K.input_stopped u n)
    filter_upwards [h1,h2] with t ht ht'
    exact Filter.EventuallyEq.trans ht ht'
  have hs : ∀ᵐ t ∂timeMeasure H, TendstoInMeasure μ (fun n ω => v n (t,ω)) atTop
      (I.integral (slice F μ H S hS hcontr M t u)) := by
    filter_upwards [ae_all_iff.mpr hApprox, timeMeasure_ae_mem H] with t ht hmem
    have hl := I.integral.continuous.continuousAt.tendsto.comp
      (approximation_input_tendsto F μ H S hS hcontr M u t hmem.1 hsem)
    have hm := tendstoInMeasure_of_tendsto_Lp hl
    exact TendstoInMeasure.congr (fun n => (ht n).symm) (Filter.EventuallyEq.rfl) hm
  have hV := ae_slices_of_slice_limits (timeMeasure H) μ v V hv
    (fun t => I.integral (slice F μ H S hS hcontr M t u)) hs
  have hA : ∀ᵐ t ∂timeMeasure H, (fun ω => V (t,ω)) =ᵐ[μ]
      (fun ω => SHE.KernelItoLimit.convolution K I u (t,ω)) :=
    Measure.ae_ae_of_ae_prod (ambient_ae _ _ (SHE.KernelItoLimit.convolution K I u))
  filter_upwards [hV,hA] with t ht ht'
  exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm ht') ht

end HeatVolterraContinuity
#check @HeatVolterraContinuity.ae_slices_of_slice_limits
#print axioms HeatVolterraContinuity.ae_slices_of_slice_limits
#check @HeatVolterraContinuity.slice_continuous
#print axioms HeatVolterraContinuity.slice_continuous
#check @HeatVolterraContinuity.integral_continuous
#print axioms HeatVolterraContinuity.integral_continuous
#check @HeatVolterraContinuity.convolution_slices
#print axioms HeatVolterraContinuity.convolution_slices
