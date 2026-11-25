import HeatTorusSobolevForm

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace HeatTorusClassicalTestAudit

open MeasureTheory UnitAddTorus HeatTorusFourier HeatTorusGradient HeatTorusAxisFourier
open scoped ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A periodic test and its classical derivatives in the physical coordinates. -/
def ClassicalTest (P : ℝ) (v : State ι) (E : ι → State ι) : Prop :=
  ∃ (φ : UnitAddTorus ι → ℂ) (dφ : ι → UnitAddTorus ι → ℂ),
    Continuous φ ∧ (∀ i, Continuous (dφ i)) ∧
    (∀ i (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => sectionAt φ i x (s : UnitAddCircle))
        ((P : ℂ) * sectionAt (dφ i) i x (t : UnitAddCircle)) t) ∧
    (v : UnitAddTorus ι → ℂ) =ᵐ[volume] φ ∧
    (∀ i, (E i : UnitAddTorus ι → ℂ) =ᵐ[volume] dφ i)

/-- Distributional integration by parts against continuous periodic tests
with continuous coordinate derivatives. -/
def DistributionalGradient (P : ℝ) (u : State ι) (D : ι → State ι) : Prop :=
  ∀ (v : State ι) (E : ι → State ι), ClassicalTest P v E →
    ∀ i, inner ℂ v (D i) = -inner ℂ (E i) u

private theorem character_section (k : ι → ℤ) (i : ι) (x : UnitAddTorus ι) (z : UnitAddCircle) :
    sectionAt (mFourier k) i x z = mFourier k x * fourier (k i) z := by
  unfold sectionAt
  have h : mFourier k (x + Pi.single i z) = mFourier k x * mFourier k (Pi.single i z) := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
      AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]
  rw [h]
  congr 1
  unfold mFourier
  simp only [ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, fourier_eval_zero]
  · exact fun h => (h (Finset.mem_univ i)).elim

private theorem character_test {P : ℝ} (hP : P ≠ 0) (k : ι → ℤ) :
    ClassicalTest P (mFourierLp 2 k) (fun i => symbol P i k • mFourierLp 2 k) := by
  refine ⟨mFourier k, fun i x => symbol P i k * mFourier k x, (mFourier k).continuous,
    fun i => continuous_const.mul (mFourier k).continuous, ?_, coeFn_mFourierLp 2 k, ?_⟩
  · intro i x t
    have hd := (hasDerivAt_fourier 1 (k i) t).const_mul (mFourier k x)
    rw [show (fun s : ℝ => sectionAt (mFourier k) i x (s : UnitAddCircle)) =
        (fun s : ℝ => mFourier k x * fourier (k i) (s : UnitAddCircle)) from
      funext fun s => character_section k i x s]
    convert hd using 1
    change (P : ℂ) * (symbol P i k * sectionAt (mFourier k) i x (t : UnitAddCircle)) = _
    rw [character_section]
    simp only [Complex.ofReal_one, div_one, symbol, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr hP]
  · intro i
    filter_upwards [Lp.coeFn_smul (symbol P i k) (mFourierLp 2 k), coeFn_mFourierLp 2 k] with x hx hk
    rw [hx, Pi.smul_apply, hk, smul_eq_mul]

omit [DecidableEq ι] in
private theorem basis_pair (v : State ι) (k : ι → ℤ) :
    inner ℂ (mFourierLp 2 k) v = mFourierCoeff v k := by
  rw [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, coe_mFourierBasis]

/-- The Fourier gradient used by the SPDE is the distributional gradient. -/
theorem iff_distributional {P : ℝ} (hP : P ≠ 0) (u : State ι) (D : ι → State ι) :
    HasGradient P u D ↔ DistributionalGradient P u D := by
  constructor
  · intro h v E hv i
    obtain ⟨φ, dφ, hφ, hdφ, hderiv, hv, hE⟩ := hv
    have hG := hasGradient_of_classical hP φ dφ hφ hdφ hderiv v E hv hE
    rw [HeatTorusSobolevForm.integration_by_parts P v u E D hG h i, neg_neg]
  · intro h i k
    have hk := h (mFourierLp 2 k) (fun j => symbol P j k • mFourierLp 2 k) (character_test hP k) i
    have hs : star (symbol P i k) = -symbol P i k := by
      simp [symbol, Complex.conj_ofReal]
    rw [inner_smul_left, basis_pair, basis_pair] at hk
    change mFourierCoeff (D i) k = -(star (symbol P i k) * mFourierCoeff u k) at hk
    rw [hs, neg_mul, neg_neg] at hk
    exact hk

end HeatTorusClassicalTestAudit

#print axioms HeatTorusClassicalTestAudit.iff_distributional
