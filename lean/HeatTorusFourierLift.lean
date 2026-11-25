import HeatTorusGradientProduct
import HeatFlatTorusSmoothLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusFourierLift

open MeasureTheory UnitAddTorus HeatFlatTorusSmoothLift HeatTorusFourier HeatTorusGradient
open HeatTorusGalerkinProjection (analysis analysis_apply)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

def phase (k : ι → ℤ) : EuclideanSpace ℝ ι →L[ℝ] ℂ :=
  ∑ i, symbol 1 i k • (Complex.ofRealCLM.comp (EuclideanSpace.proj i))

theorem character_covering (k : ι → ℤ) (x : EuclideanSpace ℝ ι) :
    mFourier k (covering 1 x) = Complex.exp (phase k x) := by
  rw [phase, sum_apply, Complex.exp_sum]
  simp only [mFourier, ContinuousMap.coe_mk]
  apply Finset.prod_congr rfl
  intro i _
  change fourier (k i) (x i : UnitAddCircle) = _
  rw [fourier_coe_apply]
  congr 1
  simp only [smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    symbol, div_one, Complex.ofReal_one]
  rw [show EuclideanSpace.proj i x = x i from rfl]
  push_cast
  ring

theorem phase_single [DecidableEq ι] (k : ι → ℤ) (i : ι) :
    phase k (EuclideanSpace.single i 1) = symbol 1 i k := by
  rw [phase, sum_apply, Finset.sum_eq_single i]
  · simp [EuclideanSpace.single]
  · intro j _ hji
    simp [EuclideanSpace.single, hji]
  · simp

/-- The Euclidean lift of a torus character has a classical derivative. -/
theorem hasFDerivAt_character (k : ι → ℤ) (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => mFourier k (covering 1 y))
      (mFourier k (covering 1 x) • phase k) x := by
  simp_rw [character_covering]
  exact (phase k).hasFDerivAt.cexp

def profile (S : Finset (ι → ℤ)) (f : State ι) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∑ k : ↥S, analysis S f k * mFourier k.val (covering 1 x)

def profileDerivative (S : Finset (ι → ℤ)) (f : State ι) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] ℂ :=
  ∑ k : ↥S, (analysis S f k * mFourier k.val (covering 1 x)) • phase k.val

theorem hasFDerivAt_profile (S : Finset (ι → ℤ)) (f : State ι) (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (profile S f) (profileDerivative S f x) x := by
  have h := HasFDerivAt.fun_sum (u := (Finset.univ : Finset ↥S))
      (fun k _ => (hasFDerivAt_character k.val x).const_smul (analysis S f k))
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_smul] at h
  exact h

theorem profileDerivative_single [DecidableEq ι] (S : Finset (ι → ℤ)) (f : State ι)
    (D : ι → State ι) (hD : HasGradient 1 f D) (x : EuclideanSpace ℝ ι) (i : ι) :
    profileDerivative S f x (EuclideanSpace.single i 1) = profile S (D i) x := by
  rw [profileDerivative, sum_apply, profile]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, phase_single, analysis_apply, analysis_apply, hD i k.val]
  simp only [smul_eq_mul]
  ring

end HeatTorusFourierLift

#print axioms HeatTorusFourierLift.hasFDerivAt_character
#print axioms HeatTorusFourierLift.hasFDerivAt_profile
#print axioms HeatTorusFourierLift.profileDerivative_single
