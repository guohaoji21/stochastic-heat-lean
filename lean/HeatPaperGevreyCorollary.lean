import HeatTorusGevreyObstruction
import HeatTorusRealMildControl

set_option autoImplicit false
noncomputable section

namespace HeatPaperGevreyCorollary

open Set UnitAddTorus HeatFlatTorusDistance HeatTorusInitialData
open scoped NNReal

private theorem geodesic_le_scaled_dist {n : ℕ} {P : ℝ} (x y : Fin n → AddCircle P) :
    distance x y ≤ Real.sqrt (n : ℝ) * dist x y := by
  have hd : 0 ≤ dist x y := dist_nonneg
  rw [distance_eq_sqrt]
  calc
    _ ≤ Real.sqrt (∑ _ : Fin n, dist x y ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ dist_nonneg ((dist_pi_le_iff hd).mp le_rfl i) 2
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hd]

private abbrev period : ℝ := 2 * Real.pi
private theorem period_pos : 0 < period := by unfold period; positivity

/-- The two parts of the paper's Gevrey corollary on the flat torus.
The ball in the observation complement uses the physical geodesic distance. -/
theorem controllability_threshold {n : ℕ} (hn : 0 < n) {O : Set (Fin n → AddCircle period)}
    (hO : IsOpen O) (hOne : O.Nonempty) (c : Fin n → AddCircle period) {r : ℝ} (hr : 0 < r)
    (hgap : {x | distance x c < r} ⊆ Oᶜ) :
    (∀ (b : (Fin n → AddCircle period) → ℝ) (C ρ : ℝ), 0 < C → 0 < ρ →
      ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0) →
      (∀ (l : List (Fin n)) x, |HeatGevreyProduct.mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x| ≤
        C * ρ ^ l.length * (l.length.factorial : ℝ)) →
      ∃ b₀ : C(UnitAddTorus (Fin n), ℂ), (∀ x, b₀ x = (b (rescale period_pos x) : ℂ)) ∧
        ∀ T : ℝ≥0, 0 < T → HeatTorusRealMildControl.NullControllable period b₀ (rescale period_pos ⁻¹' O) T) ∧
    ∀ s : ℝ, 1 < s → ∃ d : HeatTorusGevreyData.Data period_pos s O,
      HeatTorusGevreyObstruction.CanonicalObstruction period_pos d := by
  constructor
  · intro b C ρ hC hρ hreg hD
    exact HeatTorusRealMildControl.paper_gevrey_one hn b hC hρ hreg hD hO hOne
  · intro s hs
    let δ := r / (Real.sqrt (n : ℝ) + 1)
    have hscale : 0 < Real.sqrt (n : ℝ) + 1 := by positivity
    have hδ : 0 < δ := div_pos hr hscale
    have hsub : Metric.ball c δ ⊆ Oᶜ := by
      intro x hx
      apply hgap
      have hx' := (lt_div_iff₀ hscale).mp (Metric.mem_ball.mp hx)
      exact (geodesic_le_scaled_dist x c).trans_lt (calc
        _ ≤ dist x c * (Real.sqrt (n : ℝ) + 1) := by
          rw [mul_comm (Real.sqrt (n : ℝ))]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) dist_nonneg
        _ < r := hx')
    exact HeatTorusGevreyObstruction.paper_canonical_counterexample hs hO c hδ hsub

end HeatPaperGevreyCorollary

#print axioms HeatPaperGevreyCorollary.controllability_threshold
