import HeatGevreyLimit

set_option autoImplicit false
noncomputable section

namespace HeatGevreyCutoff

open HeatGevreyLimit HeatGevreyWidths Set
open scoped NNReal

/-- A Gevrey cutoff on the real line with a prescribed plateau and a
strict margin between the topological support and the exterior boundary. -/
theorem exists_cutoff {s r R : ℝ} (hs : 1 < s) (hr : 0 < r) (hR : r < R) :
    ∃ b : ℝ → ℝ, ∃ ρ : ℝ, 0 < ρ ∧ ContDiff ℝ (⊤ : ℕ∞) b ∧
      (∀ x, b x ∈ Icc 0 1) ∧ (∀ x, |x| ≤ r → b x = 1) ∧
      tsupport b ⊆ Ioo (-R) R ∧ HasCompactSupport b ∧
      ∀ (n : ℕ) x, ‖iteratedDeriv n b x‖ ≤ ρ ^ n * (n.factorial : ℝ) ^ s := by
  let δ := (R-r)/4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hR) (by norm_num)
  have hmargin : r + 3 * δ < R := by dsimp [δ]; linarith
  obtain ⟨a, ha, hasum, haj⟩ := exists_width_budget hs hδ
  let w := width a s
  have hw (n : ℕ) : 0 < w n := width_pos ha s n
  let L : ℝ≥0 := ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩
  let g : ℝ → ℝ := fun x => (r + 2 * δ - |x|) / δ
  let f : ℝ → ℝ := fun x => min 1 (max (g x) 0)
  have hg : LipschitzWith L g := LipschitzWith.of_dist_le_mul fun x y => by
    have he : g x - g y = (|y| - |x|) / δ := by dsimp only [g]; rw [← sub_div]; congr 1; ring
    rw [Real.dist_eq, Real.dist_eq, he, abs_div, abs_of_pos hδ]
    change |(|y| - |x|)| / δ ≤ δ⁻¹ * |x-y|
    calc
      _ ≤ |x-y| / δ := div_le_div_of_nonneg_right
        (by simpa only [abs_sub_comm x y] using abs_abs_sub_abs_le y x) hδ.le
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have hf : LipschitzWith L f := (hg.max_const 0).const_min 1
  have hf01 (x : ℝ) : f x ∈ Icc 0 1 :=
    ⟨le_min zero_le_one (le_max_right _ _), min_le_left _ _⟩
  have hf_one (x : ℝ) (hx : |x| ≤ r + δ) : f x = 1 := by
    have hxg : 1 ≤ g x := (le_div_iff₀ hδ).mpr (by linarith)
    exact min_eq_left (hxg.trans (le_max_left _ _))
  have hf_zero (x : ℝ) (hx : r + 2 * δ ≤ |x|) : f x = 0 := by
    have hxg : g x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hδ.le
    change min 1 (max (g x) 0) = 0
    rw [max_eq_right hxg, min_eq_right zero_le_one]
  let b := limit w f
  have hnorm (x : ℝ) : ‖f x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hf01 x).1]; exact (hf01 x).2
  have hder := limit_contDiff_and_bound hf hnorm w hw hasum
  have hplateau (x : ℝ) (hx : |x| ≤ r) : b x = 1 := by
    apply limit_eq_const hf w hw hasum
    intro y hy
    apply hf_one
    have htri : |y| ≤ |y-x| + |x| := by simpa only [sub_add_cancel] using abs_add_le (y-x) x
    linarith
  have hzero (x : ℝ) (hx : r + 3 * δ ≤ |x|) : b x = 0 := by
    apply limit_eq_const hf w hw hasum
    intro y hy
    apply hf_zero
    have htri : |x| ≤ |y-x| + |y| := by
      simpa only [sub_add_cancel, abs_sub_comm x y] using abs_add_le (x-y) y
    linarith
  have hsupport : tsupport b ⊆ Icc (-(r + 3 * δ)) (r + 3 * δ) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    apply abs_le.mp
    by_contra! hh
    exact hx (hzero x hh.le)
  refine ⟨b, a⁻¹, inv_pos.mpr ha, contDiff_infty.mpr (fun n => (hder n).1),
    limit_mem_Icc hf hf01 w hw hasum, hplateau, ?_, ?_, ?_⟩
  · intro x hx
    have hh := hsupport hx
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · exact isCompact_Icc.of_isClosed_subset isClosed_closure hsupport
  · intro n x
    calc
      _ ≤ 1 / ∏ k ∈ Finset.range n, width a s k := (hder n).2 x
      _ = _ := by rw [one_div, width_product_inv, div_eq_mul_inv, inv_pow, mul_comm]

end HeatGevreyCutoff

#print axioms HeatGevreyCutoff.exists_cutoff
