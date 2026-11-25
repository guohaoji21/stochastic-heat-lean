import HeatTorusFourier
import Mathlib.Analysis.Complex.OperatorNorm

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatTorusReal

open MeasureTheory UnitAddTorus HeatTorusFourier
open scoped ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι]

abbrev RealState (ι : Type*) [Fintype ι] :=
  Lp ℝ 2 (volume : Measure (UnitAddTorus ι))

def embed : RealState ι →L[ℝ] State ι := Complex.ofRealCLM.compLpL 2 volume

def realPart : State ι →L[ℝ] RealState ι := Complex.reCLM.compLpL 2 volume

private def conjugate : State ι →L[ℝ] State ι :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

theorem embed_ae (f : RealState ι) : embed f =ᵐ[volume] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

theorem realPart_ae (f : State ι) : realPart f =ᵐ[volume] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f

private theorem conjugate_ae (f : State ι) : conjugate f =ᵐ[volume] fun x => conj (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

theorem realPart_embed (f : RealState ι) : realPart (embed f) = f := by
  apply Lp.ext
  filter_upwards [realPart_ae (embed f), embed_ae f] with x hr he
  simp only [hr, he, Complex.ofReal_re]

private theorem embed_realPart (f : State ι) (hf : ∀ᵐ x ∂volume, (f x).im = 0) :
    embed (realPart f) = f := by
  apply Lp.ext
  filter_upwards [embed_ae (realPart f), realPart_ae f, hf] with x he hr hi
  rw [he, hr]
  apply Complex.ext <;> simp [hi]

private theorem fourierCoeff_conjugate (f : State ι) (k : ι → ℤ) :
    mFourierCoeff (conjugate f) k = conj (mFourierCoeff f (-k)) := by
  unfold mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [conjugate_ae f] with x hx
  rw [hx]
  simp only [smul_eq_mul, neg_neg, map_mul, ← mFourier_neg]

private theorem conjugate_heat (P t : ℝ) (f : State ι) :
    conjugate (heat P t f) = heat P t (conjugate f) := by
  apply (mFourierBasis (d := ι)).repr.injective
  apply lp.ext
  funext k
  simp only [mFourierBasis_repr, fourierCoeff_conjugate, fourierCoeff_heat, map_mul]
  have hfreq : frequencySquared P (-k) = frequencySquared P k := by
    simp [frequencySquared, Pi.neg_apply]
  rw [multiplier, hfreq, Complex.conj_ofReal, ← multiplier]

theorem heat_preserves_real (P t : ℝ) (f : State ι) (hf : ∀ᵐ x ∂volume, (f x).im = 0) :
    ∀ᵐ x ∂volume, (heat P t f x).im = 0 := by
  have hconj : conjugate f = f := by
    apply Lp.ext
    filter_upwards [conjugate_ae f, hf] with x hc hi
    rw [hc]
    apply Complex.ext <;> simp [hi]
  have he : conjugate (heat P t f) = heat P t f := by rw [conjugate_heat, hconj]
  have ha := conjugate_ae (heat P t f)
  rw [he] at ha
  filter_upwards [ha] with x hx
  have h := congrArg Complex.im hx
  simp only [Complex.conj_im] at h
  linarith

def realHeat (P t : ℝ) : RealState ι →L[ℝ] RealState ι :=
  realPart.comp (((heat P t).restrictScalars ℝ).comp embed)

theorem embed_realHeat (P t : ℝ) (f : RealState ι) :
    embed (realHeat P t f) = heat P t (embed f) := by
  apply embed_realPart
  apply heat_preserves_real
  filter_upwards [embed_ae f] with x hx
  change (embed f x).im = 0
  have h : embed f x = (f x : ℂ) := hx
  rw [h, Complex.ofReal_im]

theorem realHeat_zero (P : ℝ) : realHeat P 0 = ContinuousLinearMap.id ℝ (RealState ι) := by
  apply ContinuousLinearMap.ext
  intro f
  change realPart (heat P 0 (embed f)) = f
  rw [heat_zero, ContinuousLinearMap.id_apply, realPart_embed]

theorem realHeat_add (P : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    realHeat (ι := ι) P (s + t) = (realHeat P s).comp (realHeat P t) := by
  apply ContinuousLinearMap.ext
  intro f
  change realPart (heat P (s + t) (embed f)) = realPart (heat P s (embed (realHeat P t f)))
  rw [embed_realHeat, heat_add P hs ht, ContinuousLinearMap.comp_apply]

theorem realHeat_contraction (P t : ℝ) (f : RealState ι) : ‖realHeat P t f‖ ≤ ‖f‖ := by
  change ‖realPart (heat P t (embed f))‖ ≤ ‖f‖
  have hre := Complex.reCLM.norm_compLp_le (heat P t (embed f))
  have he := Complex.ofRealCLM.norm_compLp_le f
  rw [Complex.reCLM_norm, one_mul] at hre
  rw [Complex.ofRealCLM_norm, one_mul] at he
  exact hre.trans ((contraction P t (embed f)).trans he)

theorem continuous_realHeat (P : ℝ) (f : RealState ι) :
    Continuous (fun t : ℝ => realHeat P t f) :=
  realPart.continuous.comp (continuous_heat P (embed f))

theorem realHeat_injective (P t : ℝ) : Function.Injective (realHeat (ι := ι) P t) := by
  intro f g h
  have h' := congrArg (embed (ι := ι)) h
  rw [embed_realHeat, embed_realHeat] at h'
  have he := congrArg (realPart (ι := ι)) (heat_injective P t h')
  simpa only [realPart_embed] using he

theorem inner_embed_re (f g : RealState ι) :
    (inner ℂ (embed f) (embed g)).re = inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  change Complex.reCLM (∫ x, inner ℂ (embed f x) (embed g x)) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner (embed f) (embed g))]
  apply integral_congr_ae
  filter_upwards [embed_ae f, embed_ae g] with x hf hg
  rw [hf, hg]
  simp [RCLike.inner_apply', Real.inner_apply, mul_comm]

theorem realHeat_symmetric (P t : ℝ) (f g : RealState ι) :
    inner ℝ (realHeat P t f) g = inner ℝ f (realHeat P t g) := by
  rw [← inner_embed_re, ← inner_embed_re f, embed_realHeat, embed_realHeat, heat_symmetric]

end HeatTorusReal

#print axioms HeatTorusReal.realHeat_add
#print axioms HeatTorusReal.continuous_realHeat
#print axioms HeatTorusReal.realHeat_symmetric
