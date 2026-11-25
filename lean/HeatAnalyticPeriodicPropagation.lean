import HeatAnalyticStripPropagation
import HeatGevreyFourierExtension

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace HeatAnalyticPeriodicPropagation

open Set HeatAnalyticStripPropagation HeatGevreyFourierExtension

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def realLine (c v : ι → ℝ) (z : ℂ) : ι → ℂ := fun i => (c i : ℂ) + z * (v i : ℂ)

theorem differentiable_realLine (c v : ι → ℝ) : Differentiable ℂ (realLine c v) := by
  apply differentiable_pi.mpr
  intro i
  change Differentiable ℂ (fun z : ℂ => (c i : ℂ) + z * (v i : ℂ))
  fun_prop

theorem realLine_strips (c v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (ρ : ℝ) :
    MapsTo (realLine c v) (strip ρ) (tube ρ) := by
  intro z hz
  apply mem_iInter.mpr
  intro i
  change (realLine c v z i).im ∈ Ioo (-ρ) ρ
  apply abs_lt.mp
  simp only [realLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    mul_zero, zero_add, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hv i)).trans_lt hz

/-- Propagate a uniform bound from one real box to the whole real slice
of a periodic holomorphic function, with a common positive exponent. -/
theorem box_to_periodic_slice {F : (ι → ℂ) → E} {P ρ r M ε : ℝ} (hP : 0 < P)
    (hr : 0 < r) (hρ : 100 * r < ρ) (hM : 0 < M) (hε : 0 ≤ ε)
    (hF : DifferentiableOn ℂ F (tube ρ)) (hcap : ∀ z ∈ tube ρ, ‖F z‖ ≤ M)
    (hperiod : ∀ (z : ι → ℂ) (m : ι → ℤ), F (z + fun i => (P : ℂ) * (m i : ℂ)) = F z)
    (c : ι → ℝ) (hbox : ∀ x : ι → ℝ, (∀ i, |x i - c i| ≤ r) → ‖F (fun i => (x i : ℂ))‖ ≤ ε)
    (k : ℕ) (hk : P ≤ (k + 1 : ℝ) * r) (x : ι → ℝ) :
    ‖F (fun i => (x i : ℂ))‖ ≤ 289 * M * (ε / M) ^ ((1 / 2 : ℝ) ^ k) := by
  let m : ι → ℤ := fun i => ⌊(x i - c i) / P⌋
  let v : ι → ℝ := fun i => (x i - c i) / P - m i
  have hv (i : ι) : v i ∈ Icc (0 : ℝ) 1 := by
    have ha := Int.floor_le ((x i - c i) / P)
    have hb := Int.lt_floor_add_one ((x i - c i) / P)
    exact ⟨sub_nonneg.mpr ha, (sub_lt_iff_lt_add.mpr (by dsimp only [m]; linarith)).le⟩
  have hmap := realLine_strips c v (fun i => abs_le.mpr ⟨by linarith [(hv i).1], (hv i).2⟩) ρ
  have hstart (t : ℝ) (ht : |t| ≤ r) : ‖F (realLine c v t)‖ ≤ ε := by
    have hlineReal : realLine c v (t : ℂ) = fun i => ((c i + t * v i : ℝ) : ℂ) := by
      funext i
      simp [realLine]
    rw [hlineReal]
    apply hbox
    intro i
    rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (hv i).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hv i).2).trans ht
  have hout : ‖F (realLine c v P)‖ ≤ 289 * M * (ε / M) ^ ((1 / 2 : ℝ) ^ k) :=
    segment_to_interval hr hρ hM hε (hF.comp (differentiable_realLine c v).differentiableOn hmap)
      (fun z hz => hcap _ (hmap hz)) hstart k P (by rwa [abs_of_pos hP])
  have hend : realLine c v (P : ℂ) + (fun i => (P : ℂ) * (m i : ℂ)) = fun i => (x i : ℂ) := by
    funext i
    change (c i : ℂ) + (P : ℂ) * (v i : ℂ) + (P : ℂ) * (m i : ℂ) = (x i : ℂ)
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_add]
    congr 1
    dsimp only [v]
    field_simp
    <;> ring
  simpa only [← hend, hperiod] using hout

end HeatAnalyticPeriodicPropagation

#print axioms HeatAnalyticPeriodicPropagation.box_to_periodic_slice
