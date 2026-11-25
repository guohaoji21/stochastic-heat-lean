import HeatTorusOffDiagonal
import HeatBackwardNodes
import HeatObservedBackwardCell
import HeatBrownianProductMoments

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatTorusCovarianceSeparation

open MeasureTheory Set HeatTorusReal UnitAddTorus
open scoped NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

abbrev family (P : ℝ) (t : ℝ≥0) : RealState ι →L[ℝ] RealState ι := realHeat P t

theorem family_continuous (P : ℝ) (f : RealState ι) : Continuous (fun t : ℝ≥0 => family P t f) :=
  (continuous_realHeat P f).comp NNReal.continuous_coe

theorem family_contraction (P : ℝ) (t : ℝ≥0) (f : RealState ι) : ‖family P t f‖ ≤ ‖f‖ :=
  realHeat_contraction P t f

def K (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) : ℝ≥0 → RealState ι →L[ℝ] RealState ι :=
  HeatCovarianceOperator.covariance (family P) (family_continuous P) (family_contraction P) M

def gapConstant (P δ : ℝ) : ℝ := δ^2 * P^2 / 4

variable (P : ℝ) (M : RealState ι →L[ℝ] RealState ι)

theorem K_contraction (hM : ‖M‖ ≤ 1) (r : ℝ≥0) (q : RealState ι) : ‖K P M r q‖ ≤ ‖q‖ :=
  ((K P M r).le_opNorm q).trans (mul_le_of_le_one_left (norm_nonneg _)
    ((HeatCovarianceOperator.covariance_norm (family P) (family_continuous P) (family_contraction P) M r).trans hM))

theorem K_zero (q : RealState ι) : K P M 0 q = M q :=
  HeatCovarianceOperator.covariance_zero (family P) (family_continuous P) (family_contraction P) M
    (realHeat_zero P) q

variable (O D : Set (UnitAddTorus ι))

abbrev observe : RealState ι →L[ℝ] Lp ℝ 2 ((volume : Measure (UnitAddTorus ι)).restrict O) :=
  HeatRestrictionAdjoint.restriction volume O

/-- An observation bound on supported heat orbits up to a prescribed duration. -/
def OffDiagonalBound (C κ : ℝ) : Prop :=
  ∀ (r L : ℝ), 0 < L → 0 ≤ r → r ≤ L → ∀ f : RealState ι,
    (∀ᵐ x ∂volume, x ∉ D → f x = 0) →
    ‖observe O (realHeat P r f)‖ ≤ C * Real.exp (-κ / L) * ‖f‖

theorem gaussian_offDiagonal (hP : 0 < P) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y) :
    OffDiagonalBound P O D (2 * (Fintype.card ι : ℝ)) (gapConstant P δ) := by
  intro r L hL hr hrL f hf
  simpa only [gapConstant, neg_div, div_div] using
    HeatTorusOffDiagonal.restriction_heat_time_bound hP hL hr hrL O D hO hδ hsep f hf

theorem heat_K_bound_of_bound (hM : ‖M‖ ≤ 1)
    {C κ : ℝ} (hC : 0 ≤ C) (hbound : OffDiagonalBound P O D C κ)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (r h L : ℝ≥0) (hL : 0 < (L : ℝ)) (hrh : r + h ≤ L) (q : RealState ι) :
    ‖observe O (family P r (K P M h q))‖ ≤
      C * Real.exp (-κ / L) * ‖q‖ := by
  let A := HeatCovarianceOperator.integrand (family P) M h q
  let B := (observe O).comp (family P r)
  let c := C * Real.exp (-κ / L)
  have hi : IntervalIntegrable A volume 0 1 :=
    HeatCovarianceOperator.integrable (family P) (family_continuous P) (family_contraction P) M h q
  have hb (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : ‖B (A v)‖ ≤ c * ‖q‖ := by
    let a := ((1-v)*(h:ℝ)).toNNReal
    let b := (v*(h:ℝ)).toNNReal
    let f := M (family P b q)
    have ha : (a : ℝ) = (1-v)*(h:ℝ) := Real.coe_toNNReal _ (mul_nonneg (sub_nonneg.mpr hv.2) h.property)
    have htime : (r : ℝ) + a ≤ L := by
      rw [ha]
      have hbound : (r:ℝ)+(h:ℝ) ≤ L := by exact_mod_cast hrh
      calc
        _ = (r:ℝ)+(h:ℝ)-v*(h:ℝ) := by ring
        _ ≤ (r:ℝ)+(h:ℝ) := sub_le_self _ (mul_nonneg hv.1 h.property)
        _ ≤ _ := hbound
    have he : B (A v) = observe O (realHeat P ((r:ℝ)+a) f) := by
      change observe O (realHeat P r (realHeat P a f)) = _
      have hadd : realHeat (ι := ι) P ((r:ℝ)+(a:ℝ)) = (realHeat P (r:ℝ)).comp (realHeat P (a:ℝ)) :=
        realHeat_add P r.property a.property
      rw [hadd, ContinuousLinearMap.comp_apply]
    have hobs := hbound ((r : ℝ) + a) L hL (add_nonneg r.property a.property) htime f (hMsupp _)
    have hnorm : ‖f‖ ≤ ‖q‖ :=
      (M.le_of_opNorm_le hM _).trans_eq (one_mul _) |>.trans (family_contraction P b q)
    have hc : 0 ≤ c := mul_nonneg hC (Real.exp_pos _).le
    rw [he]
    exact hobs.trans (mul_le_mul_of_nonneg_left hnorm hc)
  change ‖B (∫ v in (0 : ℝ)..1, A v)‖ ≤ c * ‖q‖
  rw [← B.intervalIntegral_comp_comm hi]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun v => B (A v))
    (a := (0 : ℝ)) (b := 1) (C := c * ‖q‖) fun v hv => by
      rw [uIoc_of_le (by norm_num)] at hv
      exact hb v ⟨hv.1.le, hv.2⟩
  simpa only [sub_zero, abs_one, mul_one] using hn

theorem heat_K_bound (hP : 0 < P) (hM : ‖M‖ ≤ 1) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (r h L : ℝ≥0) (hL : 0 < (L : ℝ)) (hrh : r + h ≤ L) (q : RealState ι) :
    ‖observe O (family P r (K P M h q))‖ ≤
      (2 * (Fintype.card ι : ℝ)) * Real.exp (-gapConstant P δ / L) * ‖q‖ :=
  heat_K_bound_of_bound P M O D hM (by positivity)
    (gaussian_offDiagonal P O D hP hO hδ hsep) hMsupp r h L hL hrh q

/-- Both deterministic terms of the Brownian-product adjoint on a cell
have the same off-diagonal bound. -/
theorem state_bounds_of_bound (hM : ‖M‖ ≤ 1)
    {C κ : ℝ} (hC : 0 ≤ C) (hbound : OffDiagonalBound P O D C κ)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (h : ℕ → ℝ≥0) (N : ℕ) (g : RealState ι)
    (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0)
    {j : ℕ} (hj : j ≤ N) {r : ℝ≥0} (hr : r ≤ h j)
    (hpos : 0 < (h j : ℝ)) (hnext : h (j+1) ≤ h j) :
    let q := HeatBackwardChain.stateAt (K P M) h N g j
    let bound := C * Real.exp (-κ / (2*(h j : ℝ))) * ‖g‖
    ‖observe O (family P r q)‖ ≤ bound ∧ ‖observe O (K P M r q)‖ ≤ bound := by
  let L := 2*h j
  let bound := C * Real.exp (-κ / (L : ℝ))
  have hL : 0 < (L : ℝ) := by dsimp [L]; positivity
  have hrL : r ≤ L := hr.trans (by rw [show L = h j+h j by dsimp [L]; ring]; exact le_self_add)
  have hc : 0 ≤ bound := mul_nonneg hC (Real.exp_pos _).le
  have cap (n : ℕ) : ‖HeatBackwardChain.stateAt (K P M) h N g n‖ ≤ ‖g‖ :=
    HeatBackwardChain.norm_bound (K P M) (K_contraction P M hM) h N g n
  change ‖observe O (family P r (HeatBackwardChain.stateAt (K P M) h N g j))‖ ≤ bound * ‖g‖ ∧
    ‖observe O (K P M r (HeatBackwardChain.stateAt (K P M) h N g j))‖ ≤ bound * ‖g‖
  constructor
  · rcases eq_or_lt_of_le hj with he | hj'
    · subst j
      rw [HeatBackwardChain.terminal]
      exact hbound r L hL r.property (show (r : ℝ) ≤ L by exact_mod_cast hrL) g hg
    · have he := HeatBackwardChain.recurrence (K P M) h N g (j := j+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at he
      rw [he]
      have htime : r+h (j+1) ≤ L := (add_le_add hr hnext).trans_eq (by dsimp [L]; ring)
      exact (heat_K_bound_of_bound P M O D hM hC hbound hMsupp r (h (j+1)) L hL htime _).trans
        (mul_le_mul_of_nonneg_left (cap (j+1)) hc)
  · have he := heat_K_bound_of_bound P M O D hM hC hbound hMsupp 0 r L hL (by simpa using hrL)
      (HeatBackwardChain.stateAt (K P M) h N g j)
    have hb := he.trans (mul_le_mul_of_nonneg_left (cap j) hc)
    simpa only [family, NNReal.coe_zero, realHeat_zero, ContinuousLinearMap.id_apply] using hb

theorem state_bounds (hP : 0 < P) (hM : ‖M‖ ≤ 1) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (h : ℕ → ℝ≥0) (N : ℕ) (g : RealState ι)
    (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0)
    {j : ℕ} (hj : j ≤ N) {r : ℝ≥0} (hr : r ≤ h j)
    (hpos : 0 < (h j : ℝ)) (hnext : h (j+1) ≤ h j) :
    let q := HeatBackwardChain.stateAt (K P M) h N g j
    let C := (2 * (Fintype.card ι : ℝ)) * Real.exp (-gapConstant P δ / (2*(h j : ℝ))) * ‖g‖
    ‖observe O (family P r q)‖ ≤ C ∧ ‖observe O (K P M r q)‖ ≤ C :=
  state_bounds_of_bound P M O D hM (by positivity)
    (gaussian_offDiagonal P O D hP hO hδ hsep) hMsupp h N g hg hj hr hpos hnext

open SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped ENNReal

local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : ℝ≥0) (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T)

local notation "R" => RawCylindricalCoordinates.row F μ T (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

/-- The spatial estimates enter the actual Brownian-product adjoint via
the conditional variance of the current increment. -/
theorem observed_cell_bound_of_bound (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s))
    (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) {C κ : ℝ} (hC : 0 ≤ C)
    (hbound : OffDiagonalBound P O D C κ)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hT : ∀ n, n ≤ N → t n ≤ T)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (hpos : t (j-1) < t j)
    (hnext : t (j+1) - t j ≤ t j - t (j-1)) (s : ℝ≥0)
    (has : t (j-1) ≤ s) (hsc : s ≤ t j) :
    let h : ℝ := (t j : ℝ) - (t (j-1) : ℝ)
    (∫ ω, ‖observe O (HeatBackwardNodes.cellState (family P) (family_continuous P)
      (family_contraction P) M T W t N g j s ω)‖ ^ 2 ∂μ) ≤
      (C * ‖g‖)^2 * Real.exp (-κ / h) *
      (∏ k ∈ Finset.range (j-1), ((t (k+1) : ℝ) - (t k : ℝ))⁻¹) *
      (((s : ℝ) - (t (j-1) : ℝ)) + ((t j : ℝ) - (s : ℝ))^2) / h^2 := by
  let h : ℕ → ℝ≥0 := fun k => t k - t (k-1)
  let q := HeatBackwardChain.stateAt (K P M) h N g j
  let ζ := HeatBrownianProducts.products W t (j-1)
  let bound := C * Real.exp (-κ / (2*(h j:ℝ))) * ‖g‖
  have hp := HeatBrownianProducts.products_properties F μ T J hlocal W hW hWa t ht N hT (j-1) (by omega)
  have hproducts := HeatBrownianProductMoments.expectation F μ T J hlocal W hW hWa t ht N hT (j-1) (by omega)
  have hh : 0 < (h j:ℝ) := by
    exact_mod_cast tsub_pos_iff_lt.mpr hpos
  have hr : t j - s ≤ h j := tsub_le_tsub_left has _
  obtain ⟨hA, hB⟩ := state_bounds_of_bound P M O D hM hC hbound hMsupp h N g hg hjN hr hh
    (by simpa only [h, show j+1-1=j by omega] using hnext)
  have hA2 : ‖observe O (family P (t j-s) q)‖^2 ≤ bound^2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hB2 : ‖observe O (K P M (t j-s) q)‖^2 ≤ bound^2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  have he := HeatObservedBackwardCell.expectation F μ T J hlocal W hW (family P)
    (family_continuous P) (family_contraction P) M (observe O) has hsc (hT j hjN) ζ hp.1 hp.2 q
  change (∫ ω, ‖observe O (HeatBackwardNodes.cellState (family P) (family_continuous P)
    (family_contraction P) M T W t N g j s ω)‖^2 ∂μ) = _ at he
  rw [he]
  have hZ : 0 ≤ ∫ ω, ζ ω^2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have he₀ : 0 ≤ (s : ℝ) - (t (j-1) : ℝ) := sub_nonneg.mpr (by exact_mod_cast has)
  have hC2 : bound^2 = (C * ‖g‖)^2 * Real.exp (-κ / (h j : ℝ)) := by
    dsimp only [bound]
    rw [mul_pow, mul_pow, mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    rw [show -κ / (2 * (h j : ℝ)) + -κ / (2 * (h j : ℝ)) =
      -κ / (h j : ℝ) by field_simp; ring]
    ring
  calc
    _ ≤ (((t j:ℝ)-(t (j-1):ℝ))⁻¹)^2*(∫ ω,ζ ω^2 ∂μ)*
        (((s:ℝ)-(t (j-1):ℝ))*bound^2 + ((t j-s:ℝ≥0):ℝ)^2*bound^2) := by
      change _ ≤ _
      gcongr <;> assumption
    _ = _ := by
      rw [hC2]
      change _ * (∫ ω, HeatBrownianProducts.products W t (j-1) ω^2 ∂μ) * _ = _
      rw [hproducts]
      dsimp only [h]
      rw [NNReal.coe_sub hpos.le, NNReal.coe_sub hsc]
      simp only [div_eq_mul_inv, inv_pow]
      ring

theorem observed_cell_bound (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s))
    (P : ℝ) (hP : 0 < P) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hT : ∀ n, n ≤ N → t n ≤ T)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (hpos : t (j-1) < t j)
    (hnext : t (j+1) - t j ≤ t j - t (j-1)) (s : ℝ≥0)
    (has : t (j-1) ≤ s) (hsc : s ≤ t j) :
    let h : ℝ := (t j : ℝ) - (t (j-1) : ℝ)
    (∫ ω, ‖observe O (HeatBackwardNodes.cellState (family P) (family_continuous P)
      (family_contraction P) M T W t N g j s ω)‖ ^ 2 ∂μ) ≤
      ((2 * (Fintype.card ι : ℝ)) * ‖g‖)^2 * Real.exp (-gapConstant P δ / h) *
      (∏ k ∈ Finset.range (j-1), ((t (k+1) : ℝ) - (t k : ℝ))⁻¹) *
      (((s : ℝ) - (t (j-1) : ℝ)) + ((t j : ℝ) - (s : ℝ))^2) / h^2 :=
  observed_cell_bound_of_bound F μ T J hlocal W hW hWa P M hM O D (by positivity)
    (gaussian_offDiagonal P O D hP hO hδ hsep) hMsupp t ht N hT g hg j hj hjN hpos hnext s has hsc

end HeatTorusCovarianceSeparation

#print axioms HeatTorusCovarianceSeparation.heat_K_bound
#print axioms HeatTorusCovarianceSeparation.state_bounds
#print axioms HeatTorusCovarianceSeparation.observed_cell_bound

#print axioms HeatTorusCovarianceSeparation.observed_cell_bound_of_bound
