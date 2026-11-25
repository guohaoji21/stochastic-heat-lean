import HeatTorusGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusSobolevFourier

open MeasureTheory UnitAddTorus HeatTorusFourier HeatTorusGradient
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

/-- The quadratic energy of one Fourier coefficient in the physical metric. -/
def modeEnergy (P : ℝ) (u : State ι) (k : ι → ℤ) : ℝ :=
  frequencySquared P k * ‖mFourierCoeff u k‖ ^ 2

theorem modeEnergy_nonneg (P : ℝ) (u : State ι) (k : ι → ℤ) : 0 ≤ modeEnergy P u k :=
  mul_nonneg (frequencySquared_nonneg P k) (sq_nonneg _)

theorem sum_symbol_sq (P : ℝ) (k : ι → ℤ) :
    (∑ i, ‖symbol P i k‖ ^ 2) = frequencySquared P k := by
  have he (i : ι) : ‖symbol P i k‖ ^ 2 = (2 * Real.pi / P) ^ 2 * (k i : ℝ) ^ 2 := by
    rw [symbol, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, mul_pow]
  simp_rw [he, ← Finset.mul_sum, frequencySquared]

private theorem derivative_weight_le (P : ℝ) (u : State ι) (i : ι) (k : ι → ℤ) :
    ‖symbol P i k * mFourierCoeff u k‖ ^ 2 ≤ modeEnergy P u k := by
  classical
  have hs : ‖symbol P i k‖ ^ 2 ≤ frequencySquared P k := by
    rw [← sum_symbol_sq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖symbol P j k‖) (Finset.mem_univ i)
  rw [modeEnergy, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)

/-- Finite total Fourier energy gives genuine spatial derivatives in `L²`. -/
theorem exists_gradient (P : ℝ) (u : State ι) (hu : Summable (modeEnergy P u)) :
    ∃ D : ι → State ι, HasGradient P u D := by
  have hsum (i : ι) : Summable (fun k : ι → ℤ => ‖symbol P i k * mFourierCoeff u k‖ ^ 2) :=
    hu.of_nonneg_of_le (fun _ => sq_nonneg _) (derivative_weight_le P u i)
  let c (i : ι) : lp (fun _ : ι → ℤ => ℂ) 2 := ⟨fun k => symbol P i k * mFourierCoeff u k,
    memℓp_gen (by simpa using hsum i)⟩
  refine ⟨fun i => (mFourierBasis (d := ι)).repr.symm (c i), ?_⟩
  intro i k
  rw [← mFourierBasis_repr]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Conversely, a Fourier `L²` gradient has exactly the weighted energy. -/
theorem gradient_energy (P : ℝ) (u : State ι) (D : ι → State ι) (hD : HasGradient P u D) :
    Summable (modeEnergy P u) ∧ (∑ i, ‖D i‖ ^ 2) = ∑' k, modeEnergy P u k := by
  have hsum (i : ι) : Summable (fun k : ι → ℤ => ‖mFourierCoeff (D i) k‖ ^ 2) := by
    have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp
      (lp.memℓp ((mFourierBasis (d := ι)).repr (D i)))
    simpa [mFourierBasis_repr] using h
  have hmode (k : ι → ℤ) : (∑ i, ‖mFourierCoeff (D i) k‖ ^ 2) = modeEnergy P u k := by
    have hspec (i : ι) := hD i k
    simp_rw [hspec, norm_mul, mul_pow]
    rw [← Finset.sum_mul, sum_symbol_sq]
    rfl
  constructor
  · classical
    have hs (s : Finset ι) : Summable (fun k : ι → ℤ => ∑ i ∈ s, ‖mFourierCoeff (D i) k‖ ^ 2) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hsum i).add ih
    simpa only [hmode] using hs Finset.univ
  · have hnorm (i : ι) : ‖D i‖ ^ 2 = ∑' k : ι → ℤ, ‖mFourierCoeff (D i) k‖ ^ 2 := by
      simpa [mFourierBasis_repr] using
        (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (mFourierBasis.repr (D i)))
    simpa only [hnorm, hmode] using
      (Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => hsum i)).symm

end HeatTorusSobolevFourier

#print axioms HeatTorusSobolevFourier.exists_gradient
#print axioms HeatTorusSobolevFourier.gradient_energy
