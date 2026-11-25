import HeatWeakRawIntegral
import HeatControlConvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatWeakDeterministicConvolution
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatIntervalNormalization
open HeatWeakDirichlet HeatConcreteSemigroupInput
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology

def value (H : ℝ≥0) (f : ℝ≥0 → Base) (t : ℝ≥0) : Base :=
  ∫ s,(if s<t then family (t-s) (f s) else 0) ∂timeMeasure H

theorem weak_equation (H : ℝ≥0) (f : ℝ≥0 → Base) (hfm : Measurable f)
    (hfi : Integrable f (timeMeasure H)) (φ ψ : Base) (hφ : weakLaplacian φ ψ) :
    Integrable (fun t => inner ℝ ψ (value H f t)) (timeMeasure H) ∧
      inner ℝ φ (value H f H)=(∫ t,inner ℝ φ (f t) ∂timeMeasure H)+
        (∫ t,inner ℝ ψ (value H f t) ∂timeMeasure H) := by
  let raw : ℝ≥0 × ℝ≥0 → Base := fun p => if p.2<p.1 then family (p.1-p.2) (f p.2) else 0
  have hm : Measurable raw := by
    have hu : Measurable (fun p : ℝ≥0 × Unit => f p.1) := hfm.comp measurable_fst
    have hh := HeatVolterraKernel.raw_measurable family (ContinuousLinearMap.id ℝ Base)
      family_continuous family_contraction (fun p : ℝ≥0 × Unit => f p.1) hu
    have hg : Measurable (fun p : ℝ≥0 × ℝ≥0 => (p.1,(p.2,()))) :=
      measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
    exact hh.comp hg
  have hbound (p : ℝ≥0 × ℝ≥0) : ‖raw p‖≤‖f p.2‖ := by
    dsimp only [raw]
    split_ifs
    · exact family_contraction _ _
    · simpa only [norm_zero] using norm_nonneg (f p.2)
  have hi : Integrable raw ((timeMeasure H).prod (timeMeasure H)) :=
    (hfi.norm.comp_snd (timeMeasure H)).mono' hm.stronglyMeasurable.aestronglyMeasurable (Eventually.of_forall hbound)
  have hslice (t : ℝ≥0) : Integrable (fun s => raw (t,s)) (timeMeasure H) :=
    hfi.norm.mono' ((hm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable)
      (Eventually.of_forall (fun s => hbound (t,s)))
  have hj : Integrable (fun p : ℝ≥0 × ℝ≥0 => inner ℝ ψ (raw p)) ((timeMeasure H).prod (timeMeasure H)) :=
    hi.const_inner ψ
  have hinner (t : ℝ≥0) : inner ℝ ψ (value H f t)=∫ s,inner ℝ ψ (raw (t,s)) ∂timeMeasure H :=
    (integral_inner (𝕜 := ℝ) (hslice t) ψ).symm
  have htest : Integrable (fun t => inner ℝ ψ (value H f t)) (timeMeasure H) :=
    hj.integral_prod_left.congr (Eventually.of_forall (fun t => (hinner t).symm))
  have hswap : (∫ t,inner ℝ ψ (value H f t) ∂timeMeasure H)=
      ∫ s,(inner ℝ φ (raw (H,s))-(if s<H then inner ℝ φ (f s) else 0)) ∂timeMeasure H := by
    calc
      _ = ∫ t,∫ s,inner ℝ ψ (raw (t,s)) ∂timeMeasure H ∂timeMeasure H :=
        integral_congr_ae (Eventually.of_forall hinner)
      _ = ∫ s,∫ t,inner ℝ ψ (raw (t,s)) ∂timeMeasure H ∂timeMeasure H := integral_integral_swap hj
      _ = _ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro s
        exact HeatWeakRawIntegral.integral_raw (fun p : ℝ≥0 × Unit => f p.1)
          (ContinuousLinearMap.id ℝ Base) φ ψ hφ H (s,())
  have ht : (fun s => if s<H then inner ℝ φ (f s) else 0)=ᵐ[timeMeasure H] fun s => inner ℝ φ (f s) := by
    filter_upwards [timeMeasure_ae_mem H,(timeMeasure H).ae_ne H] with s hs hne
    exact if_pos (lt_of_le_of_ne hs.2 hne)
  rw [integral_sub ((hslice H).const_inner φ) ((hfi.const_inner φ).congr ht.symm),
    integral_congr_ae ht] at hswap
  have hh := integral_inner (𝕜 := ℝ) (hslice H) φ
  change (∫ s,inner ℝ φ (raw (H,s)) ∂timeMeasure H)=inner ℝ φ (value H f H) at hh
  rw [hh] at hswap
  exact ⟨htest,by linarith⟩

end HeatWeakDeterministicConvolution
#check @HeatWeakDeterministicConvolution.weak_equation
#print HeatWeakDeterministicConvolution.weak_equation
#print axioms HeatWeakDeterministicConvolution.weak_equation
