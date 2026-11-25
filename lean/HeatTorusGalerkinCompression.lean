import HeatTorusGalerkinProjection
import SHEStochastic.BoundedFieldOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace HeatTorusGalerkinCompression

open Filter MeasureTheory UnitAddTorus SHEStochastic.BoundedFieldOperator
open HeatTorusGalerkinProjection (analysis synthesis project)
open HeatTorusGalerkinBackward (State)
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local notation "Full" => HeatTorusFourier.State ι
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)

private def coefficientField (b : C(UnitAddTorus ι, ℂ)) :
    Field (volume : Measure (UnitAddTorus ι)) ℂ ℂ where
  value x := ContinuousLinearMap.mul ℝ ℂ (b x)
  measurable := (ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable
    b.continuous.aestronglyMeasurable
  bound := ‖b‖₊
  norm_bound := Eventually.of_forall fun x => by
    apply (ContinuousLinearMap.mul ℝ ℂ (b x)).opNorm_le_bound (norm_nonneg b)
    intro z
    change ‖b x * z‖ ≤ ‖b‖ * ‖z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (b.norm_coe_le_norm x) (norm_nonneg z)

/-- Spatial multiplication by the actual coefficient on full Haar L². -/
def fullMultiplier (b : C(UnitAddTorus ι, ℂ)) : Full →L[ℝ] Full :=
  operator (coefficientField b)

theorem fullMultiplier_ae (b : C(UnitAddTorus ι, ℂ)) (f : Full) :
    (fullMultiplier b f : UnitAddTorus ι → ℂ) =ᵐ[volume] fun x => b x * f x :=
  operator_ae (coefficientField b) f

theorem fullMultiplier_norm (b : C(UnitAddTorus ι, ℂ)) : ‖fullMultiplier b‖ ≤ ‖b‖ :=
  operator_norm (coefficientField b)

theorem synthesis_ae (S : Finset (ι → ℤ)) (x : State S) :
    (synthesis S x : UnitAddTorus ι → ℂ) =ᵐ[volume]
      fun z => ∑ k : ↥S, x k * mFourier k.val z := by
  rw [HeatTorusGalerkinProjection.synthesis_apply]
  apply (Lp.coeFn_fun_finsetSum Finset.univ (fun k : ↥S => x k • mFourierLp 2 k.val)).trans
  have h (k : ↥S) : ((x k • mFourierLp 2 k.val : Full) : UnitAddTorus ι → ℂ) =ᵐ[volume]
      fun z => x k * mFourier k.val z :=
    (Lp.coeFn_smul _ _).trans ((coeFn_mFourierLp 2 k.val).fun_comp (fun y : ℂ => x k * y))
  filter_upwards [ae_all_iff.mpr h] with z h
  exact Finset.sum_congr rfl fun k _ => h k

/-- The finite noise matrix is exactly the compression of the full
multiplication operator between Fourier analysis and synthesis. -/
theorem multiplier_eq (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) (x : State S) :
    HeatTorusGalerkinBackward.multiplier S b x = analysis S (fullMultiplier b (synthesis S x)) := by
  ext k
  rw [HeatTorusGalerkinProjection.analysis_apply, ← HeatTorusGalerkinBackward.coefficient_mul]
  unfold mFourierCoeff
  apply integral_congr_ae
  filter_upwards [fullMultiplier_ae b (synthesis S x), synthesis_ae S x] with z hm hs
  rw [hm, hs]

theorem multiplier_norm (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) :
    ‖HeatTorusGalerkinBackward.multiplier S b‖ ≤ ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [multiplier_eq]
  calc
    _ ≤ ‖fullMultiplier b (synthesis S x)‖ := HeatTorusGalerkinProjection.analysis_contraction _ _
    _ ≤ ‖b‖ * ‖synthesis S x‖ := (fullMultiplier b).le_of_opNorm_le (fullMultiplier_norm b) _
    _ = _ := by rw [HeatTorusGalerkinProjection.synthesis_norm]

theorem fullMultiplier_symmetric (b : C(UnitAddTorus ι, ℂ)) (hb : ∀ z, (b z).im = 0) (x y : Full) :
    inner ℝ (fullMultiplier b x) y = inner ℝ x (fullMultiplier b y) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fullMultiplier_ae b x, fullMultiplier_ae b y] with z hx hy
  rw [hx, hy]
  change (inner ℂ (b z * x z) (y z)).re = (inner ℂ (x z) (b z * y z)).re
  simp only [RCLike.inner_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hb]
  ring

private theorem inner_full_re (f g : Full) : inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) f g)

theorem analysis_inner (S : Finset (ι → ℤ)) (f : Full) (x : State S) :
    inner ℝ (analysis S f) x = inner ℝ f (synthesis S x) := by
  calc
    _ = inner ℝ x (analysis S f) := real_inner_comm _ _
    _ = inner ℝ (synthesis S x) f := by
      rw [inner_full_re]
      exact congrArg Complex.re ((synthesis S).adjoint_inner_right x f)
    _ = _ := real_inner_comm _ _

theorem multiplier_symmetric (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ))
    (hb : ∀ z, (b z).im = 0) (x y : State S) :
    inner ℝ (HeatTorusGalerkinBackward.multiplier S b x) y =
      inner ℝ x (HeatTorusGalerkinBackward.multiplier S b y) := by
  rw [multiplier_eq, multiplier_eq]
  calc
    _ = inner ℝ (fullMultiplier b (synthesis S x)) (synthesis S y) := analysis_inner _ _ _
    _ = inner ℝ (synthesis S x) (fullMultiplier b (synthesis S y)) := fullMultiplier_symmetric b hb _ _
    _ = inner ℝ (analysis S (fullMultiplier b (synthesis S y))) x :=
      (real_inner_comm _ _).trans (analysis_inner _ _ _).symm
    _ = _ := real_inner_comm _ _

theorem laplace_symmetric (S : Finset (ι → ℤ)) (P : ℝ) (x y : State S) :
    inner ℝ (HeatTorusGalerkinBackward.laplace S P x) y =
      inner ℝ x (HeatTorusGalerkinBackward.laplace S P y) := by
  change (inner ℂ (HeatTorusGalerkinBackward.laplace S P x) y).re =
    (inner ℂ x (HeatTorusGalerkinBackward.laplace S P y)).re
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k : ↥S, y k * star (HeatTorusGalerkinBackward.laplace S P x k)).re =
    (∑ k : ↥S, HeatTorusGalerkinBackward.laplace S P y k * star (x k)).re
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [HeatTorusGalerkinBackward.laplace_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem laplace_nonpos (S : Finset (ι → ℤ)) (P : ℝ) (x : State S) :
    inner ℝ (HeatTorusGalerkinBackward.laplace S P x) x ≤ 0 := by
  change (inner ℂ (HeatTorusGalerkinBackward.laplace S P x) x).re ≤ 0
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k : ↥S, x k * star (HeatTorusGalerkinBackward.laplace S P x k)).re ≤ 0
  rw [show (∑ k : ↥S, x k * star (HeatTorusGalerkinBackward.laplace S P x k)).re =
      ∑ k : ↥S, (x k * star (HeatTorusGalerkinBackward.laplace S P x k)).re from map_sum Complex.reCLM _ _]
  apply Finset.sum_nonpos
  intro k _
  rw [HeatTorusGalerkinBackward.laplace_apply]
  have h : (x k * star (((-HeatTorusFourier.frequencySquared P k.val : ℝ) : ℂ) * x k)).re =
      -HeatTorusFourier.frequencySquared P k.val * ‖x k‖ ^ 2 := by
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [h]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (HeatTorusFourier.frequencySquared_nonneg P _)) (sq_nonneg _)

/-- The extra diffusion created by projecting the full equation is exactly
the effect of the discarded part of the forward state. -/
theorem diffusion_defect (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) (x : Full) :
    analysis S (fullMultiplier b x) - HeatTorusGalerkinBackward.multiplier S b (analysis S x) =
      analysis S (fullMultiplier b (x - project S x)) := by
  rw [multiplier_eq, map_sub, map_sub]
  rfl

theorem diffusion_defect_norm (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) (x : Full) :
    ‖analysis S (fullMultiplier b x) - HeatTorusGalerkinBackward.multiplier S b (analysis S x)‖ ≤
      ‖b‖ * ‖x - project S x‖ := by
  rw [diffusion_defect]
  exact (HeatTorusGalerkinProjection.analysis_contraction _ _).trans
    ((fullMultiplier b).le_of_opNorm_le (fullMultiplier_norm b) _)

end HeatTorusGalerkinCompression

#print axioms HeatTorusGalerkinCompression.multiplier_eq
#print axioms HeatTorusGalerkinCompression.multiplier_norm
#print axioms HeatTorusGalerkinCompression.multiplier_symmetric
#print axioms HeatTorusGalerkinCompression.laplace_symmetric
#print axioms HeatTorusGalerkinCompression.laplace_nonpos
#print axioms HeatTorusGalerkinCompression.diffusion_defect_norm
