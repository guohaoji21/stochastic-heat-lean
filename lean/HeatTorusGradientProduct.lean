import HeatTorusGradient
import HeatTorusGalerkinCompression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace HeatTorusGradientProduct

open MeasureTheory Filter UnitAddTorus HeatTorusFourier HeatTorusGradient
open HeatTorusAxisFourier (sectionAt)
open HeatTorusGalerkinProjection (analysis project)
open HeatTorusGalerkinCompression (fullMultiplier fullMultiplier_ae synthesis_ae)
open scoped Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

private def profile (S : Finset (ι → ℤ)) (f : State ι) (x : UnitAddTorus ι) : ℂ :=
  ∑ k : ↥S, analysis S f k * mFourier k.val x

private theorem profile_continuous (S : Finset (ι → ℤ)) (f : State ι) :
    Continuous (profile S f) :=
  continuous_finsetSum _ fun k _ => continuous_const.mul (mFourier k.val).continuous

private theorem profile_ae (S : Finset (ι → ℤ)) (f : State ι) :
    (project S f : UnitAddTorus ι → ℂ) =ᵐ[volume] profile S f :=
  synthesis_ae S (analysis S f)

variable [DecidableEq ι]

private theorem character_axis (k : ι → ℤ) (i : ι) (x : UnitAddTorus ι) (z : UnitAddCircle) :
    sectionAt (mFourier k) i x z = mFourier k x * fourier (k i) z := by
  have hsingle : mFourier k (Pi.single i z) = fourier (k i) z := by
    unfold mFourier
    simp only [ContinuousMap.coe_mk]
    rw [Finset.prod_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, fourier_eval_zero]
    · exact fun h => (h (Finset.mem_univ i)).elim
  rw [sectionAt, ← hsingle]
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private theorem profile_derivative {P : ℝ} (hP : P ≠ 0)
    (S : Finset (ι → ℤ)) (f : State ι) (D : ι → State ι) (hf : HasGradient P f D)
    (i : ι) (x : UnitAddTorus ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sectionAt (profile S f) i x (s : UnitAddCircle))
      ((P : ℂ) * sectionAt (profile S (D i)) i x (t : UnitAddCircle)) t := by
  have hscale (k : ι → ℤ) : (P : ℂ) * symbol P i k = 2 * (Real.pi : ℂ) * Complex.I * k i := by
    unfold symbol
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hP]
    <;> ring
  have hterm (k : ↥S) :
      HasDerivAt (fun s : ℝ => analysis S f k * sectionAt (mFourier k.val) i x (s : UnitAddCircle))
        ((P : ℂ) * (analysis S (D i) k * sectionAt (mFourier k.val) i x (t : UnitAddCircle))) t := by
    have h := (hasDerivAt_fourier 1 (k.val i) t).const_mul (analysis S f k * mFourier k.val x)
    have hk : analysis S (D i) k = symbol P i k.val * analysis S f k := by
      rw [HeatTorusGalerkinProjection.analysis_apply, HeatTorusGalerkinProjection.analysis_apply]
      exact hf i k.val
    simp_rw [character_axis]
    rw [hk]
    convert h using 1
    · funext s
      ring
    · simp only [Complex.ofReal_one, div_one]
      linear_combination (analysis S f k * mFourier k.val x * fourier (k.val i) (t : UnitAddCircle)) *
        hscale k.val
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset ↥S)) (fun k _ => hterm k)
  convert h using 1
  · rfl
  · simp only [profile, sectionAt, Finset.mul_sum]

/-- Multiplication by a continuously differentiable periodic function
satisfies the product rule on the full Fourier gradient domain. -/
theorem product {P : ℝ} (hP : P ≠ 0)
    (a : C(UnitAddTorus ι, ℂ)) (da : ι → C(UnitAddTorus ι, ℂ))
    (ha : ∀ i (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => sectionAt a i x (s : UnitAddCircle))
        ((P : ℂ) * sectionAt (da i) i x (t : UnitAddCircle)) t)
    (f : State ι) (D : ι → State ι) (hf : HasGradient P f D) :
    HasGradient P (fullMultiplier a f)
      (fun i => fullMultiplier (da i) f + fullMultiplier a (D i)) := by
  have hfinite (S : Finset (ι → ℤ)) :
      HasGradient P (fullMultiplier a (project S f))
        (fun i => fullMultiplier (da i) (project S f) + fullMultiplier a (project S (D i))) := by
    let v (x : UnitAddTorus ι) := a x * profile S f x
    let dv (i : ι) (x : UnitAddTorus ι) := da i x * profile S f x + a x * profile S (D i) x
    apply hasGradient_of_classical hP v dv (a.continuous.mul (profile_continuous S f))
      (fun i => ((da i).continuous.mul (profile_continuous S f)).add
        (a.continuous.mul (profile_continuous S (D i))))
    · intro i x t
      convert (ha i x t).mul (profile_derivative hP S f D hf i x t) using 1
      · rfl
      · simp only [dv, sectionAt]
        ring
    · filter_upwards [fullMultiplier_ae a (project S f), profile_ae S f] with x hx hb
      rw [hx, hb]
    · intro i
      filter_upwards [Lp.coeFn_add (fullMultiplier (da i) (project S f))
        (fullMultiplier a (project S (D i))), fullMultiplier_ae (da i) (project S f),
        fullMultiplier_ae a (project S (D i)), profile_ae S f, profile_ae S (D i)]
        with x hsum h₁ h₂ h₃ h₄
      rw [hsum, Pi.add_apply, h₁, h₂, h₃, h₄]
  intro i k
  have hF := (((fullMultiplier a).continuous.tendsto f).comp
    (HeatTorusGalerkinProjection.project_tendsto f))
  have hD := (((fullMultiplier (da i)).continuous.tendsto f).comp
    (HeatTorusGalerkinProjection.project_tendsto f)).add
      (((fullMultiplier a).continuous.tendsto (D i)).comp
        (HeatTorusGalerkinProjection.project_tendsto (D i)))
  have hFc := ((coefficientCLM k).continuous.continuousAt.tendsto.comp hF).const_mul (symbol P i k)
  have hDc := (coefficientCLM k).continuous.continuousAt.tendsto.comp hD
  simp only [Function.comp_def, coefficientCLM_apply] at hFc hDc
  have hEq (S : Finset (ι → ℤ)) := hfinite S i k
  simp only [hEq] at hDc
  exact tendsto_nhds_unique hDc hFc

end HeatTorusGradientProduct

#print axioms HeatTorusGradientProduct.product
