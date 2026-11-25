import HeatBoundaryDerivative
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatSineH01
open MeasureTheory Filter Set HeatBoundaryCutoff HeatBoundaryDerivative
open HeatWeakDirichlet HeatIntervalNormalization EllipticPdes
open scoped Topology ENNReal

local instance : IsFiniteMeasure (volume.restrict domain) := by
  unfold domain
  infer_instance

def width (m : ℕ) : ℝ := 1/((m : ℝ)+3)

theorem width_pos (m : ℕ) : 0 < width m := by unfold width; positivity

theorem width_lt_five (m : ℕ) : width m < 5 := by
  unfold width
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [div_lt_iff₀ (by positivity : 0 < (m : ℝ)+3)]
  linarith

theorem width_tendsto : Tendsto width atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  convert h using 1
  funext m
  simp [width, Function.comp_def, Nat.cast_add, Nat.cast_ofNat, add_assoc] <;> norm_num

theorem approximation_test (m : ℕ) (k : ℝ) : approximation (width m) k ∈ testFunctions domain := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (approximation (width m) k) := by
    unfold approximation
    exact (cutoff_smooth _).mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))
  have hsub : tsupport (approximation (width m) k) ⊆ Set.Icc (width m) (10-width m) :=
    tsupport_mul_subset_left.trans (cutoff_support _ (width_pos m))
  refine ⟨hs, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsub, ?_⟩
  intro x hx
  have ht := hsub hx
  exact ⟨lt_of_lt_of_le (width_pos m) ht.1, lt_of_le_of_lt ht.2 (by linarith [width_pos m])⟩

theorem eventually_inside (x : ℝ) (hx : x ∈ domain) :
    ∀ᶠ m in atTop, 2*width m ≤ x ∧ x ≤ 10-2*width m := by
  have hl := (tendsto_order.mp width_tendsto).2 (x/2) (by linarith [hx.1])
  have hr := (tendsto_order.mp width_tendsto).2 ((10-x)/2) (by linarith [hx.2])
  filter_upwards [hl,hr] with m h1 h2
  constructor <;> linarith

theorem approximation_tendsto (k x : ℝ) (hx : x ∈ domain) :
    Tendsto (fun m => approximation (width m) k x) atTop (𝓝 (Real.sin (k*x))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_inside x hx] with m hm
  simp [approximation, cutoff_one _ _ (width_pos m) hm.1 hm.2]

theorem approximationDerivative_tendsto (k x : ℝ) (hx : x ∈ domain) :
    Tendsto (fun m => approximationDerivative (width m) k x) atTop (𝓝 (k*Real.cos (k*x))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_inside x hx] with m hm
  have h1 : 1 ≤ x/width m-1 := by
    have := (le_div_iff₀ (width_pos m)).mpr hm.1
    linarith
  have h2 : 1 ≤ (10-x)/width m-1 := by
    have := (le_div_iff₀ (width_pos m)).mpr (show 2*width m ≤ 10-x by linarith [hm.2])
    linarith
  simp [approximationDerivative, cutoff_one _ _ (width_pos m) hm.1 hm.2, cutoffDerivative,
    step_derivative_zero_right _ h1, step_derivative_zero_right _ h2]

theorem bounded_L2_convergence {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F : ℕ → X → ℝ) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ m, AEStronglyMeasurable (F m) μ) (hf : MemLp f 2 μ)
    (hbound : ∀ m, ∀ᵐ x ∂μ, |F m x| ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun m => F m x) atTop (𝓝 (f x))) :
    Tendsto (fun m => eLpNorm (F m-f) 2 μ) atTop (𝓝 0) := by
  have hconst : MemLp (fun _ : X => B) 2 μ := memLp_const B
  have hui : UnifIntegrable F 2 μ := by
    apply (unifIntegrable_const (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hconst).ae_mono hF
    intro m
    filter_upwards [hbound m] with x hx
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
      coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hB]
    exact hx
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hF hf hui hlim

theorem sine_memLp (k : ℝ) : MemLp (fun x : ℝ => Real.sin (k*x)) 2 (volume.restrict domain) := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (k*x)

theorem sineGradient_memLp (k : ℝ) : MemLp (fun x : ℝ => k*Real.cos (k*x)) 2 (volume.restrict domain) := by
  apply MemLp.of_bound (by fun_prop) |k|
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)

def sine (k : ℝ) : Base := (sine_memLp k).toLp (fun x => Real.sin (k*x))
def sineGradient (k : ℝ) : Base := (sineGradient_memLp k).toLp (fun x => k*Real.cos (k*x))

theorem sine_ae (k : ℝ) : (sine k : ℝ → ℝ) =ᵐ[volume.restrict domain] (fun x => Real.sin (k*x)) :=
  (sine_memLp k).coeFn_toLp

theorem sineGradient_ae (k : ℝ) : (sineGradient k : ℝ → ℝ) =ᵐ[volume.restrict domain] (fun x => k*Real.cos (k*x)) :=
  (sineGradient_memLp k).coeFn_toLp

theorem sineGraph_mem_H01 (k : ℝ) (hend : Real.sin (k*10) = 0) :
    H1Graph.mk (sine k) (sineGradient k) ∈ H1Graph.H01 volume domain := by
  obtain ⟨C,hC0,hC⟩ := step_derivative_bounded
  let φ : ℕ → testFunctions domain := fun m => ⟨approximation (width m) k, approximation_test m k⟩
  let Φ : ℕ → H1Graph volume domain := fun m => H1Graph.testGraphₗ volume domain (φ m)
  have hf : ∀ m, (H1Graph.fnL (Φ m) : ℝ → ℝ) =ᵐ[volume.restrict domain] approximation (width m) k :=
    fun m => H1Graph.coeFn_fnL_testGraphₗ (φ m)
  have hg : ∀ m, (H1Graph.gradL (Φ m) : ℝ → ℝ) =ᵐ[volume.restrict domain] approximationDerivative (width m) k := by
    intro m
    filter_upwards [H1Graph.coeFn_gradL_testGraphₗ (φ m)] with x hx
    rw [hx, gradient_eq_deriv']
    exact (approximation_hasDerivAt (width m) k x).deriv
  have hfm : ∀ m, AEStronglyMeasurable (approximation (width m) k) (volume.restrict domain) :=
    fun m => (φ m).property.1.continuous.aestronglyMeasurable
  have hgm : ∀ m, AEStronglyMeasurable (approximationDerivative (width m) k) (volume.restrict domain) := by
    intro m
    have hc : Continuous (deriv (approximation (width m) k)) := (φ m).property.1.continuous_deriv (by simp)
    have he : deriv (approximation (width m) k) = approximationDerivative (width m) k :=
      funext fun x => (approximation_hasDerivAt (width m) k x).deriv
    rw [he] at hc
    exact hc.aestronglyMeasurable
  have hflim : Tendsto (fun m => eLpNorm (approximation (width m) k - fun x => Real.sin (k*x)) 2
      (volume.restrict domain)) atTop (𝓝 0) := by
    apply bounded_L2_convergence _ _ _ 1 (by norm_num) hfm (sine_memLp k)
    · intro m
      filter_upwards [] with x
      rw [approximation, abs_mul, abs_of_nonneg (cutoff_bounds _ _).1]
      exact (mul_le_mul (cutoff_bounds _ _).2 (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact approximation_tendsto k x hx
  have hglim : Tendsto (fun m => eLpNorm (approximationDerivative (width m) k - fun x => k*Real.cos (k*x)) 2
      (volume.restrict domain)) atTop (𝓝 0) := by
    apply bounded_L2_convergence _ _ _ ((4*C+1)*|k|) (by positivity) hgm (sineGradient_memLp k)
    · intro m
      exact Filter.Eventually.of_forall fun x => approximationDerivative_bound C hC _ k x (width_pos m) hend
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact approximationDerivative_tendsto k x hx
  have hlim := H1Graph.tendsto_mk_of_tendsto_eLpNorm (Φ := Φ) (sine_memLp k) (sineGradient_memLp k) hf hg hflim hglim
  exact H1Graph.isClosed_H01.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun m => H1Graph.testGraphₗ_mem_H01 (φ m))

end HeatSineH01
#check @HeatSineH01.width_pos
#print axioms HeatSineH01.width_pos
#check @HeatSineH01.width_lt_five
#print axioms HeatSineH01.width_lt_five
#check @HeatSineH01.width_tendsto
#print axioms HeatSineH01.width_tendsto
#check @HeatSineH01.approximation_test
#print axioms HeatSineH01.approximation_test
#check @HeatSineH01.eventually_inside
#print axioms HeatSineH01.eventually_inside
#check @HeatSineH01.approximation_tendsto
#print axioms HeatSineH01.approximation_tendsto
#check @HeatSineH01.approximationDerivative_tendsto
#print axioms HeatSineH01.approximationDerivative_tendsto
#check @HeatSineH01.bounded_L2_convergence
#print axioms HeatSineH01.bounded_L2_convergence

#check @HeatSineH01.sine_memLp
#print axioms HeatSineH01.sine_memLp
#check @HeatSineH01.sineGradient_memLp
#print axioms HeatSineH01.sineGradient_memLp
#check @HeatSineH01.sine_ae
#print axioms HeatSineH01.sine_ae
#check @HeatSineH01.sineGradient_ae
#print axioms HeatSineH01.sineGradient_ae
#check @HeatSineH01.sineGraph_mem_H01
#print axioms HeatSineH01.sineGraph_mem_H01
