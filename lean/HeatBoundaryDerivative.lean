import HeatBoundaryCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatBoundaryDerivative
open HeatBoundaryCutoff Set MeasureTheory

def cutoffDerivative (a x : ℝ) : ℝ :=
  deriv Real.smoothTransition (x/a-1)/a * Real.smoothTransition ((10-x)/a-1) -
    Real.smoothTransition (x/a-1) * (deriv Real.smoothTransition ((10-x)/a-1)/a)

theorem cutoff_hasDerivAt (a x : ℝ) : HasDerivAt (cutoff a) (cutoffDerivative a x) x := by
  have hd (y : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition y) y :=
    ((@Real.smoothTransition.contDiff (⊤ : ℕ∞)).differentiable (by simp) y).hasDerivAt
  have hl := (hd (x/a-1)).comp x (((hasDerivAt_id x).div_const a).sub_const 1)
  have hr := (hd ((10-x)/a-1)).comp x ((((hasDerivAt_id x).const_sub 10).div_const a).sub_const 1)
  convert hl.mul hr using 1
  · funext y; rfl
  · dsimp only [cutoffDerivative, Function.comp_def, id_eq]; ring

theorem step_weight_bound (C : ℝ) (hC : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    (a K x w : ℝ) (ha : 0 < a) (hK : 0 ≤ K) (hw : |w| ≤ K*|x|) :
    |deriv Real.smoothTransition (x/a-1)/a * w| ≤ 2*C*K := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  by_cases hz : deriv Real.smoothTransition (x/a-1) = 0
  · rw [hz, zero_div, zero_mul, abs_zero]
    positivity
  · have hm := step_derivative_support (subset_closure hz)
    have hx0 : 0 ≤ x := by have := (le_div_iff₀ ha).mp (show 0 ≤ x/a by linarith [hm.1]); simpa using this
    have hx2 : x ≤ 2*a := (div_le_iff₀ ha).mp (by linarith [hm.2])
    have hww : |w| ≤ K*(2*a) := hw.trans (mul_le_mul_of_nonneg_left (by rwa [abs_of_nonneg hx0]) hK)
    rw [abs_mul, abs_div, abs_of_pos ha]
    calc
      _ ≤ (C/a) * (K*(2*a)) := mul_le_mul
        (div_le_div_of_nonneg_right (hC _) ha.le) hww (abs_nonneg _) (div_nonneg hC0 ha.le)
      _ = 2*C*K := by field_simp <;> ring

theorem cutoffDerivative_wave_bound (C : ℝ) (hC : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    (a k x : ℝ) (ha : 0 < a) (hend : Real.sin (k*10) = 0) :
    |cutoffDerivative a x * Real.sin (k*x)| ≤ 4*C*|k| := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hl : |deriv Real.smoothTransition (x/a-1)/a * Real.sin (k*x)| ≤ 2*C*|k| := by
    apply step_weight_bound C hC a |k| x _ ha (abs_nonneg _)
    simpa only [abs_mul] using Real.abs_sin_le_abs (x := k*x)
  have hr : |deriv Real.smoothTransition ((10-x)/a-1)/a * Real.sin (k*x)| ≤ 2*C*|k| := by
    apply step_weight_bound C hC a |k| (10-x) _ ha (abs_nonneg _)
    have hs := Real.abs_sin_sub_sin_le (k*x) (k*10)
    rw [hend, sub_zero, ← mul_sub, abs_mul, abs_sub_comm] at hs
    exact hs
  have hθ (y : ℝ) : |Real.smoothTransition y| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg y)]
    exact Real.smoothTransition.le_one y
  unfold cutoffDerivative
  rw [sub_mul]
  calc
    _ ≤ |(deriv Real.smoothTransition (x/a-1)/a * Real.smoothTransition ((10-x)/a-1)) * Real.sin (k*x)| +
      |(Real.smoothTransition (x/a-1) * (deriv Real.smoothTransition ((10-x)/a-1)/a)) * Real.sin (k*x)| := abs_sub _ _
    _ = |deriv Real.smoothTransition (x/a-1)/a * Real.sin (k*x)| * |Real.smoothTransition ((10-x)/a-1)| +
      |deriv Real.smoothTransition ((10-x)/a-1)/a * Real.sin (k*x)| * |Real.smoothTransition (x/a-1)| := by
      simp only [abs_mul]; ring
    _ ≤ (2*C*|k|)*1 + (2*C*|k|)*1 := by gcongr <;> first | exact hl | exact hr | exact hθ _ | positivity
    _ = 4*C*|k| := by ring

def approximation (a k x : ℝ) : ℝ := cutoff a x * Real.sin (k*x)
def approximationDerivative (a k x : ℝ) : ℝ :=
  cutoffDerivative a x * Real.sin (k*x) + cutoff a x * (k * Real.cos (k*x))

theorem approximation_hasDerivAt (a k x : ℝ) :
    HasDerivAt (approximation a k) (approximationDerivative a k x) x := by
  have hs := (Real.hasDerivAt_sin (k*x)).comp x ((hasDerivAt_id x).const_mul k)
  convert (cutoff_hasDerivAt a x).mul hs using 1
  · funext y; rfl
  · dsimp only [approximationDerivative, Function.comp_def]; ring

theorem approximationDerivative_bound (C : ℝ) (hC : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    (a k x : ℝ) (ha : 0 < a) (hend : Real.sin (k*10) = 0) :
    |approximationDerivative a k x| ≤ (4*C+1)*|k| := by
  have ht : |cutoff a x * (k * Real.cos (k*x))| ≤ |k| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_bounds a x).1]
    calc
      _ ≤ 1 * (|k| *1) := by gcongr; exact (cutoff_bounds a x).2; exact Real.abs_cos_le_one _
      _ = |k| := by ring
  unfold approximationDerivative
  exact (abs_add_le _ _).trans (by nlinarith [cutoffDerivative_wave_bound C hC a k x ha hend])

end HeatBoundaryDerivative
#check @HeatBoundaryDerivative.cutoff_hasDerivAt
#print axioms HeatBoundaryDerivative.cutoff_hasDerivAt
#check @HeatBoundaryDerivative.step_weight_bound
#print axioms HeatBoundaryDerivative.step_weight_bound
#check @HeatBoundaryDerivative.cutoffDerivative_wave_bound
#print axioms HeatBoundaryDerivative.cutoffDerivative_wave_bound
#check @HeatBoundaryDerivative.approximation_hasDerivAt
#print axioms HeatBoundaryDerivative.approximation_hasDerivAt
#check @HeatBoundaryDerivative.approximationDerivative_bound
#print axioms HeatBoundaryDerivative.approximationDerivative_bound
