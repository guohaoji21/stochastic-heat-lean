import HeatAnalyticObservedNorm
import HeatTorusModeEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace HeatTorusObservedPolynomial

open Filter MeasureTheory Set UnitAddTorus SHE.PredictableL2
open HeatTorusGalerkinBackward (State modeProjection)
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι]

section Polynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {S : Finset (ι → ℤ)}

/-- A finite Fourier polynomial with Hilbert-space coefficients. -/
def polynomial (c : ↥S → E) : C(UnitAddTorus ι, E) :=
  ⟨fun x => ∑ k, mFourier k.val x • c k,
    continuous_finsetSum _ (fun k _ => (mFourier k.val).continuous.smul continuous_const)⟩

omit [CompleteSpace E] in
theorem memLp (c : ↥S → E) : MemLp (polynomial c) 2 (volume : Measure (UnitAddTorus ι)) :=
  (polynomial c).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem orthogonality (k l : ↥S) :
    (∫ x : UnitAddTorus ι, inner ℂ (mFourier k.val x) (mFourier l.val x)) =
      if k = l then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι))) k.val l.val
  rw [ContinuousMap.inner_toLp] at h
  simpa only [RCLike.inner_apply, Subtype.val_inj] using h

/-- Normalized Haar Parseval for a finite Hilbert-space Fourier polynomial. -/
theorem integral_norm_sq (c : ↥S → E) :
    (∫ x : UnitAddTorus ι, ‖polynomial c x‖ ^ 2) = ∑ k, ‖c k‖ ^ 2 := by
  classical
  let a (k l : ↥S) (x : UnitAddTorus ι) := inner ℂ (mFourier k.val x) (mFourier l.val x)
  let t (k l : ↥S) (x : UnitAddTorus ι) := a k l x * inner ℂ (c k) (c l)
  have hi (k l : ↥S) : Integrable (t k l) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · change Continuous (fun x => inner ℂ (mFourier k.val x) (mFourier l.val x) * inner ℂ (c k) (c l))
      exact ((mFourier k.val).continuous.inner (mFourier l.val).continuous).mul continuous_const
    · exact HasCompactSupport.of_compactSpace _
  have hs (x : UnitAddTorus ι) : inner ℂ (polynomial c x) (polynomial c x) = ∑ k, ∑ l, t k l x := by
    change inner ℂ (∑ k, mFourier k.val x • c k) (∑ l, mFourier l.val x • c l) = _
    rw [sum_inner]
    simp only [inner_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp only [inner_smul_right, inner_smul_left, t, a, RCLike.inner_apply]
    ring
  have hsum : (∫ x : UnitAddTorus ι, inner ℂ (polynomial c x) (polynomial c x)) =
      ∑ k, inner ℂ (c k) (c k) := by
    simp_rw [hs, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hi k l))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum _ (fun l _ => hi k l)]
    have ht (l : ↥S) : (∫ x : UnitAddTorus ι, t k l x) =
        (if k = l then 1 else 0) * inner ℂ (c k) (c l) := by
      rw [show (fun x => t k l x) = fun x => a k l x * inner ℂ (c k) (c l) from rfl,
        integral_mul_const, orthogonality]
    simp only [ht, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
  have hint : Integrable (fun x => inner ℂ (polynomial c x) (polynomial c x)) volume :=
    ((polynomial c).continuous.inner (polynomial c).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := congrArg Complex.reCLM hsum
  rw [← Complex.reCLM.integral_comp_comm hint, map_sum] at h
  have hreal_inner (y : E) : (inner ℂ y y).re = ‖y‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  simpa only [Complex.reCLM_apply, hreal_inner] using h

end Polynomial

section RandomCoefficients

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : Finset (ι → ℤ)}

local instance : InnerProductSpace ℝ (Lp ℂ 2 μ) := InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 μ)

/-- The actual random Fourier coordinate, as a scalar random variable in L². -/
def coordinate (X : Lp (State S) 2 μ) (k : ↥S) : Lp ℂ 2 μ :=
  ((EuclideanSpace.proj (𝕜 := ℂ) k).compLpL 2 μ) X

theorem coordinate_ae (X : Lp (State S) 2 μ) (k : ↥S) :
    (coordinate X k : Ω → ℂ) =ᵐ[μ] (fun ω => X ω k) :=
  (EuclideanSpace.proj (𝕜 := ℂ) k).coeFn_compLpL X

theorem coordinate_norm_sq (X : Lp (State S) 2 μ) (k : ↥S) :
    ‖coordinate X k‖ ^ 2 = ‖((modeProjection S k).compLpL 2 μ) X‖ ^ 2 := by
  rw [realLp_norm_sq, HeatTorusModeEnergy.integral_mode_energy]
  apply integral_congr_ae
  filter_upwards [coordinate_ae X k] with ω hω using congrArg (fun z : ℂ => ‖z‖ ^ 2) hω

theorem global_energy (X : Lp (State S) 2 μ) :
    (∫ x : UnitAddTorus ι, ‖polynomial (coordinate X) x‖ ^ 2) = ‖X‖ ^ 2 := by
  simp_rw [integral_norm_sq, coordinate_norm_sq]
  exact HeatTorusModeEnergy.sum_mode_energy X

/-- Spatial observation of the reconstructed Galerkin state in mean square. -/
def observedEnergy (O : Set (UnitAddTorus ι)) (X : Lp (State S) 2 μ) : ℝ :=
  ∫ x in O, ‖polynomial (coordinate X) x‖ ^ 2

theorem observedEnergy_eq_integral (O : Set (UnitAddTorus ι)) (X : Lp (State S) 2 μ) :
    observedEnergy O X = ∫ x in O, ∫ ω, ‖∑ k : ↥S, mFourier k.val x * X ω k‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change ‖(∑ k : ↥S, mFourier k.val x • coordinate X k)‖ ^ 2 = _
  rw [realLp_norm_sq]
  apply integral_congr_ae
  have hk (k : ↥S) : ((mFourier k.val x • coordinate X k : Lp ℂ 2 μ) : Ω → ℂ) =ᵐ[μ]
      (fun ω => mFourier k.val x * X ω k) :=
    (Lp.coeFn_smul _ _).trans ((coordinate_ae X k).fun_comp (fun z : ℂ => mFourier k.val x * z))
  filter_upwards [(Lp.coeFn_fun_finsetSum Finset.univ (fun k : ↥S => mFourier k.val x • coordinate X k)),
    ae_all_iff.mpr hk] with ω hsum hcoord
  have hsum' : ((∑ k : ↥S, mFourier k.val x • coordinate X k : Lp ℂ 2 μ) : Ω → ℂ) ω =
      ∑ k : ↥S, mFourier k.val x * X ω k :=
    hsum.trans (Finset.sum_congr rfl (fun k _ => hcoord k))
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hsum'

/-- The deterministic analytic interpolation inequality applies to the actual
random Fourier polynomial via its Hilbert-space-valued coefficients. -/
theorem spatial_interpolation {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C K θ : ℝ, 0 < C ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (S : Finset (ι → ℤ)) (X : Lp (State S) 2 μ) (M : ℝ), 0 < M →
        (∑ k : ↥S, Real.exp (2 * ρ * HeatGevreyFourierExtension.weight k.val) *
          ‖((modeProjection S k).compLpL 2 μ) X‖ ^ 2) ≤ M ^ 2 →
        ‖X‖ ^ 2 ≤ C * (M * K) ^ 2 * ((observedEnergy O X / (M * K) ^ 2) ^ θ) := by
  classical
  obtain ⟨C, K, θ, hC, hK, hθ, hθ₁, h⟩ :=
    HeatAnalyticObservedNorm.weighted_fourier_interpolation (E := Lp ℂ 2 μ) hO hOne hρ
  refine ⟨C, K, θ, hC, hK, hθ, hθ₁, ?_⟩
  intro S X M hM hX
  let c (k : ι → ℤ) : Lp ℂ 2 μ := if hk : k ∈ S then coordinate X ⟨k, hk⟩ else 0
  let g := polynomial (coordinate X)
  let f (k : ι → ℤ) := Real.exp (2 * ρ * HeatGevreyFourierExtension.weight k) * ‖c k‖ ^ 2
  have hc (k : ↥S) : c k.val = coordinate X k := dite_eq_left k.property
  have hcap (B : Finset (ι → ℤ)) : ∑ k ∈ B, f k ≤ M ^ 2 := by
    calc
      _ = ∑ k ∈ B ∩ S, f k := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro k hk hks
        have hnot : k ∉ S := fun hmem => hks (Finset.mem_inter.mpr ⟨hk, hmem⟩)
        simp only [f, c, dite_eq_right hnot, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      _ ≤ ∑ k ∈ S, f k := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun k _ _ => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
      _ ≤ _ := by
        rw [← Finset.sum_coe_sort S]
        simpa only [f, hc, coordinate_norm_sq] using hX
  have hreal (x : ι → ℝ) : g (HeatTorusGaussian.wrap x) =
      ∑' k, mFourier k (HeatTorusGaussian.wrap x) • c k := by
    rw [tsum_eq_sum (s := S) (fun k hk => by simp [c, hk]), ← Finset.sum_coe_sort S]
    simp only [hc]
    rfl
  have hg := memLp (coordinate X)
  have hnorm {m : Measure (UnitAddTorus ι)} (hg' : MeasureTheory.MemLp g 2 m) :
      ‖hg'.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂m := by
    rw [realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hg'.coeFn_toLp] with x hx
    rw [hx]
  have he := h c g hg M hM hcap hreal
  rw [hnorm hg, hnorm (hg.restrict O)] at he
  simpa only [g, global_energy, observedEnergy] using he

end RandomCoefficients

end HeatTorusObservedPolynomial

#print axioms HeatTorusObservedPolynomial.integral_norm_sq
#print axioms HeatTorusObservedPolynomial.coordinate_norm_sq
#print axioms HeatTorusObservedPolynomial.global_energy
#print axioms HeatTorusObservedPolynomial.observedEnergy_eq_integral
#print axioms HeatTorusObservedPolynomial.spatial_interpolation
