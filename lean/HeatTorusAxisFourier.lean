import HeatTorusFourierDerivatives
import HeatGevreyFourierDecay

set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section

namespace HeatTorusAxisFourier

open MeasureTheory Complex UnitAddTorus HeatTorusFourierDerivatives

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (AddCircle.haarAddCircle (T := 1)).IsAddHaarMeasure
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sectionAt (f : UnitAddTorus ι → ℂ) (i : ι) (x : UnitAddTorus ι) (z : UnitAddCircle) : ℂ :=
  f (x + Pi.single i z)

private theorem continuous_single (i : ι) : Continuous (fun z : UnitAddCircle => (Pi.single i z : UnitAddTorus ι)) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    have he : (fun z : UnitAddCircle => (Pi.single i z : UnitAddTorus ι) i) = id := by
      funext z
      simp only [Pi.single_eq_same, id_eq]
    rw [he]
    exact continuous_id
  · simpa only [Pi.single_eq_of_ne h] using (continuous_const : Continuous (fun _ : UnitAddCircle => (0 : UnitAddCircle)))

private theorem character_single (k : ι → ℤ) (i : ι) (z : UnitAddCircle) :
    mFourier k (Pi.single i z) = fourier (k i) z := by
  unfold mFourier
  simp only [ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, fourier_eval_zero]
  · exact fun h => (h (Finset.mem_univ i)).elim

private theorem mean_section (f : UnitAddTorus ι → ℂ) (hf : Continuous f) (i : ι) (k : ι → ℤ) :
    (∫ x, mFourier (-k) x * fourierCoeff (sectionAt f i x) (k i)) = mFourierCoeff f k := by
  let H : UnitAddTorus ι → UnitAddCircle → ℂ :=
    fun x z => mFourier (-k) x * (fourier (-(k i)) z * f (x + Pi.single i z))
  have hH : Continuous (Function.uncurry H) := by
    exact ((mFourier (-k)).continuous.comp continuous_fst).mul
      (((fourier (-k i)).continuous.comp continuous_snd).mul
        (hf.comp (continuous_fst.add ((continuous_single i).comp continuous_snd))))
  have hi : Integrable (Function.uncurry H)
      ((volume : Measure (UnitAddTorus ι)).prod (volume : Measure UnitAddCircle)) :=
    hH.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  calc
    _ = ∫ x, ∫ z, H x z := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change mFourier (-k) x * fourierCoeff (sectionAt f i x) (k i) = ∫ z, H x z
      unfold fourierCoeff
      rw [← integral_const_mul]
      rfl
    _ = ∫ z, ∫ x, H x z := integral_integral_swap hi
    _ = _ := by
      have hh (z : UnitAddCircle) : (∫ x, H x z) = mFourierCoeff f k := by
        have he (x : UnitAddTorus ι) :
            mFourier (-k) (x + Pi.single i z) = mFourier (-k) x * fourier (-(k i)) z := by
          have h : mFourier (-k) (x + Pi.single i z) =
              mFourier (-k) x * mFourier (-k) (Pi.single i z) := by
            simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
              AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]
          rw [h, character_single, Pi.neg_apply]
        let e : UnitAddTorus ι ≃ᵐ UnitAddTorus ι := MeasurableEquiv.addRight (Pi.single i z)
        let A : UnitAddTorus ι → ℂ := fun x => mFourier (-k) x * f x
        have hμ : MeasurePreserving e volume volume :=
          HeatTorusGaussian.translation_preserving (Pi.single i z)
        have hpt (x : UnitAddTorus ι) : H x z = A (e x) := by
          simp only [H, A, e, MeasurableEquiv.coe_addRight, he x, mul_assoc]
        have hi' : (∫ x, H x z) = ∫ x, A (e x) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
        have he' : (∫ x, A (e x)) = ∫ x, A x :=
          hμ.integral_comp' (f := e) A
        unfold mFourierCoeff
        simpa only [A, smul_eq_mul] using hi'.trans he'
      rw [show (∫ z, ∫ x, H x z) = ∫ _ : UnitAddCircle, mFourierCoeff f k from
        integral_congr_ae (Filter.Eventually.of_forall hh), integral_const, probReal_univ, one_smul]

/-- The coordinate derivative multiplies the multidimensional Fourier
coefficient by the corresponding frequency, for a general continuous function. -/
theorem coefficient_derivative (f f' : UnitAddTorus ι → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (i : ι) (hd : ∀ (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun u : ℝ => sectionAt f i x (u : UnitAddCircle))
        (sectionAt f' i x (t : UnitAddCircle)) t) (k : ι → ℤ) :
    mFourierCoeff f' k = (2 * Real.pi * I * k i) * mFourierCoeff f k := by
  rw [← mean_section f' hf' i k, ← mean_section f hf i k, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hc : Continuous (sectionAt f' i x) := hf'.comp (continuous_const.add (continuous_single i))
  have he := HeatTorusFourierDerivatives.coefficient_derivative (sectionAt f i x) (sectionAt f' i x)
    hc (hd x) (k i)
  change mFourier (-k) x * fourierCoeff (sectionAt f' i x) (k i) = _
  rw [he]
  ring

theorem iterated_coefficient (f : ℕ → UnitAddTorus ι → ℂ) (hf : ∀ n, Continuous (f n))
    (i : ι) (hd : ∀ n (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun u : ℝ => sectionAt (f n) i x (u : UnitAddCircle))
        (sectionAt (f (n + 1)) i x (t : UnitAddCircle)) t) (k : ι → ℤ) (n : ℕ) :
    mFourierCoeff (f n) k = (2 * Real.pi * I * k i)^n * mFourierCoeff (f 0) k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [coefficient_derivative (f n) (f (n + 1)) (hf n) (hf (n + 1)) i (hd n) k, ih, pow_succ']
    ring

/-- A common factorial bound on the coordinate derivatives gives decay
exponential in the sum of the absolute coordinate frequencies. -/
theorem exponential_decay [Nonempty ι] (b : UnitAddTorus ι → ℂ)
    (f : ι → ℕ → UnitAddTorus ι → ℂ) (hbase : ∀ i, f i 0 = b)
    (hf : ∀ i n, Continuous (f i n))
    (hd : ∀ i n (x : UnitAddTorus ι) (t : ℝ),
      HasDerivAt (fun u : ℝ => sectionAt (f i n) i x (u : UnitAddCircle))
        (sectionAt (f i (n + 1)) i x (t : UnitAddCircle)) t)
    (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hbound : ∀ i n x, ‖f i n x‖ ≤ C * ρ^n * (n.factorial : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ k : ι → ℤ,
      ‖mFourierCoeff b k‖ ≤ 2 * C * Real.exp (-a * ∑ i, |(k i : ℝ)|) := by
  let B := Real.log 2 / (2 * ρ) * (2 * Real.pi)
  have hB : 0 < B := by dsimp [B]; positivity
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨B / (Fintype.card ι : ℝ), div_pos hB hcard, ?_⟩
  intro k
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |(k i : ℝ)|) Finset.univ_nonempty
  have hmode : ‖(2 * Real.pi * I * k i : ℂ)‖ = 2 * Real.pi * |(k i : ℝ)| := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast]
  have hc (n : ℕ) : (2 * Real.pi * |(k i : ℝ)|)^n * ‖mFourierCoeff b k‖ ≤
      C * ρ^n * (n.factorial : ℝ) := by
    have h := iterated_coefficient (f i) (hf i) i (hd i) k n
    rw [hbase i] at h
    have hnorm := congrArg norm h
    rw [norm_mul, norm_pow, hmode] at hnorm
    rw [← hnorm]
    unfold mFourierCoeff
    have hb (x : UnitAddTorus ι) : ‖mFourier (-k) x • f i n x‖ ≤ C * ρ^n * (n.factorial : ℝ) := by
      rw [norm_smul]
      have hχ : ‖mFourier (-k) x‖ = 1 := by
        simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
          Finset.prod_const_one]
      rw [hχ, one_mul]
      exact hbound i n x
    simpa only [integral_const, probReal_univ, one_smul] using
      norm_integral_le_of_norm_le (integrable_const (μ := (volume : Measure (UnitAddTorus ι)))
        (C * ρ^n * (n.factorial : ℝ)))
        (Filter.Eventually.of_forall hb)
  have h := HeatGevreyFourierDecay.exponential_bound ‖mFourierCoeff b k‖ C ρ
    (2 * Real.pi * |(k i : ℝ)|) hC hρ (by positivity) hc
  have hsum : (∑ j, |(k j : ℝ)|) ≤ (Fintype.card ι : ℝ) * |(k i : ℝ)| := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := (Finset.univ : Finset ι)) hi
  have he : -(Real.log 2 / (2 * ρ)) * (2 * Real.pi * |(k i : ℝ)|) ≤
      -(B / (Fintype.card ι : ℝ)) * ∑ j, |(k j : ℝ)| := by
    rw [neg_mul, neg_mul, neg_le_neg_iff, show Real.log 2 / (2 * ρ) * (2 * Real.pi * |(k i : ℝ)|) =
      B * |(k i : ℝ)| by dsimp [B]; ring]
    have hh : (∑ j, |(k j : ℝ)|) / (Fintype.card ι : ℝ) ≤ |(k i : ℝ)| :=
      (div_le_iff₀ hcard).2 (by simpa only [mul_comm] using hsum)
    convert mul_le_mul_of_nonneg_left hh hB.le using 1
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))

end HeatTorusAxisFourier

#print axioms HeatTorusAxisFourier.coefficient_derivative
#print axioms HeatTorusAxisFourier.iterated_coefficient
#print axioms HeatTorusAxisFourier.exponential_decay
