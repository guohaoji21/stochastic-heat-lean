import HeatTorusFourierDerivatives

set_option autoImplicit false
set_option maxHeartbeats 2300000
noncomputable section

namespace HeatTorusTensorGenerator

open MeasureTheory UnitAddTorus HeatTorusFourier HeatTorusReal HeatTorusFourierDerivatives

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

/-- Fourier coefficients factor on tensor products with normalized Haar measure. -/
theorem coefficient_tensor (f : ι → UnitAddCircle → ℂ) (k : ι → ℤ) :
    mFourierCoeff (fun x => ∏ i, f i (x i)) k = ∏ i, fourierCoeff (f i) (k i) := by
  unfold mFourierCoeff fourierCoeff
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, smul_eq_mul,
    ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_volume_eq_prod
    (fun (i : ι) (x : UnitAddCircle) => fourier (-k i) x * f i x)

variable [DecidableEq ι]

def tensor {𝕜 : Type*} [CommMonoid 𝕜] (f : ι → UnitAddCircle → 𝕜) (x : UnitAddTorus ι) : 𝕜 :=
  ∏ i, f i (x i)

def second {𝕜 : Type*} [CommRing 𝕜] (f f'' : ι → UnitAddCircle → 𝕜) (x : UnitAddTorus ι) : 𝕜 :=
  ∑ i, f'' i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j)

theorem continuous_tensor {𝕜 : Type*} [CommMonoid 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (f : ι → UnitAddCircle → 𝕜) (hf : ∀ i, Continuous (f i)) : Continuous (tensor f) :=
  continuous_finsetProd _ fun i _ => (hf i).comp (continuous_apply i)

theorem continuous_second {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜]
    [ContinuousMul 𝕜] [ContinuousAdd 𝕜] (f f'' : ι → UnitAddCircle → 𝕜)
    (hf : ∀ i, Continuous (f i)) (hf'' : ∀ i, Continuous (f'' i)) :
    Continuous (second f f'') :=
  continuous_finsetSum _ fun i _ => ((hf'' i).comp (continuous_apply i)).mul
    (continuous_finsetProd _ fun j _ => (hf j).comp (continuous_apply j))

theorem coefficient_second (f f'' : ι → UnitAddCircle → ℂ)
    (hf : ∀ i, Continuous (f i)) (hf'' : ∀ i, Continuous (f'' i)) (k : ι → ℤ)
    (hcoeff : ∀ i, fourierCoeff (f'' i) (k i) =
      (↑(-((2 * Real.pi : ℝ)^2 * (k i : ℝ)^2)) : ℂ) * fourierCoeff (f i) (k i)) :
    mFourierCoeff (second f f'') k =
      (↑(-((2 * Real.pi : ℝ)^2 * ∑ i, (k i : ℝ)^2)) : ℂ) * mFourierCoeff (tensor f) k := by
  let R := fun i (x : UnitAddTorus ι) => f'' i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j)
  have hR (i : ι) : Continuous (R i) := ((hf'' i).comp (continuous_apply i)).mul
    (continuous_finsetProd _ fun j _ => (hf j).comp (continuous_apply j))
  have hsum : mFourierCoeff (second f f'') k = ∑ i, mFourierCoeff (R i) k := by
    unfold mFourierCoeff second
    simp only [smul_eq_mul, Finset.mul_sum]
    apply integral_finsetSum
    intro i _
    apply Continuous.integrable_of_hasCompactSupport
    · exact (mFourier (-k)).continuous.mul (hR i)
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)
  rw [hsum, show mFourierCoeff (tensor f) k = ∏ i, fourierCoeff (f i) (k i) from
    coefficient_tensor f k]
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_intCast, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hr : R i = tensor (Function.update f i (f'' i)) := by
    funext x
    unfold tensor
    have he (j : ι) : Function.update f i (f'' i) j (x j) =
        Function.update (fun l => f l (x l)) i (f'' i (x i)) j := by
      by_cases hj : j = i <;> simp [hj]
    simp only [he, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, R]
  rw [hr, show mFourierCoeff (tensor (Function.update f i (f'' i))) k = _ from
    coefficient_tensor (Function.update f i (f'' i)) k]
  have hi (j : ι) : fourierCoeff (Function.update f i (f'' i) j) (k j) =
      Function.update (fun l => fourierCoeff (f l) (k l)) i (fourierCoeff (f'' i) (k i)) j := by
    by_cases hj : j = i <;> simp [hj]
  simp only [hi, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  rw [hcoeff i, mul_assoc, Finset.mul_prod_erase Finset.univ
    (fun j => fourierCoeff (f j) (k j)) (Finset.mem_univ i)]
  push_cast <;> ring

/-- The real (L^2) generator of a tensor product is the sum of its
coordinate second derivatives, rescaled to the physical period. -/
theorem generator_tensor (P : ℝ) (f f' f'' : ι → UnitAddCircle → ℝ)
    (hf : ∀ i, Continuous (f i)) (hf' : ∀ i, Continuous (f' i)) (hf'' : ∀ i, Continuous (f'' i))
    (hd : ∀ i (x : ℝ), HasDerivAt (fun y : ℝ => f i (y : UnitAddCircle)) (f' i (x : UnitAddCircle)) x)
    (hdd : ∀ i (x : ℝ), HasDerivAt (fun y : ℝ => f' i (y : UnitAddCircle)) (f'' i (x : UnitAddCircle)) x)
    (F G : RealState ι) (hF : (F : UnitAddTorus ι → ℝ) =ᵐ[volume] tensor f)
    (hG : (G : UnitAddTorus ι → ℝ) =ᵐ[volume] fun x => P⁻¹ ^ 2 * second f f'' x) :
    HasDerivWithinAt (fun s : ℝ => realHeat P s F) G (Set.Ici 0) 0 := by
  apply (HeatTorusSubeigen.generator_iff_coefficients P F G).mpr
  intro k
  let toC := fun (a : ι → UnitAddCircle → ℝ) i x => (a i x : ℂ)
  have hFc : mFourierCoeff (embed F) k = mFourierCoeff (tensor (toC f)) k := by
    unfold mFourierCoeff
    apply integral_congr_ae
    filter_upwards [embed_ae F, hF] with x he hx
    rw [he, hx]
    simp only [tensor, toC, Complex.ofReal_prod]
  have hGc : mFourierCoeff (embed G) k = (↑(P⁻¹ ^ 2 : ℝ) : ℂ) *
      mFourierCoeff (second (toC f) (toC f'')) k := by
    unfold mFourierCoeff
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [embed_ae G, hG] with x he hx
    rw [he, hx]
    simp only [toC, second, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_prod, smul_eq_mul]
    ring
  have hc (i : ι) := coefficient_second_derivative (toC f i) (toC f' i) (toC f'' i)
    (Complex.continuous_ofReal.comp (hf' i)) (Complex.continuous_ofReal.comp (hf'' i))
    (fun x => (hd i x).ofReal_comp) (fun x => (hdd i x).ofReal_comp) (k i)
  rw [hFc, hGc, coefficient_second (toC f) (toC f'') (fun i => Complex.continuous_ofReal.comp (hf i))
    (fun i => Complex.continuous_ofReal.comp (hf'' i)) k hc]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  unfold frequencySquared
  rw [div_eq_mul_inv]
  ring

end HeatTorusTensorGenerator

#print axioms HeatTorusTensorGenerator.coefficient_tensor
#print axioms HeatTorusTensorGenerator.generator_tensor
