import HeatTorusGalerkinProjection
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace HeatTorusFrequencyExhaustion

open Filter MeasureTheory Set UnitAddTorus SHE.PredictableL2
open HeatTorusGalerkinProjection (project)
open scoped Topology ENNReal

variable {ι : Type*} [Fintype ι]

local notation "Full" => HeatTorusFourier.State ι

/-- Symmetric, increasing boxes of Fourier frequencies. -/
def box (ι : Type*) [Fintype ι] (N : ℕ) : Finset (ι → ℤ) :=
  (Set.Finite.pi' (fun _ : ι => Set.finite_Icc (-(N : ℤ)) (N : ℤ))).toFinset

theorem mem_box (N : ℕ) (k : ι → ℤ) : k ∈ box ι N ↔ ∀ i, |k i| ≤ (N : ℤ) := by
  simp only [box, Set.Finite.mem_toFinset, mem_ofPred_eq, mem_Icc, abs_le]

theorem neg_mem_box (N : ℕ) (k : ι → ℤ) : -k ∈ box ι N ↔ k ∈ box ι N := by
  simp only [mem_box, Pi.neg_apply, abs_neg]

theorem box_cofinal : Tendsto (box ι) atTop atTop := by
  classical
  refine tendsto_atTop.2 fun S => ?_
  filter_upwards [eventually_ge_atTop (∑ k ∈ S, ∑ i, (k i).natAbs)] with N hN
  intro k hk
  rw [mem_box]
  intro i
  have hni : (k i).natAbs ≤ N := calc
    _ ≤ ∑ j, (k j).natAbs := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ ∑ l ∈ S, ∑ j, (l j).natAbs :=
      Finset.single_le_sum (f := fun l : ι → ℤ => ∑ j, (l j).natAbs) (fun _ _ => Nat.zero_le _) hk
    _ ≤ _ := hN
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hni

theorem frequency_outside (N : ℕ) (P : ℝ) {k : ι → ℤ} (hk : k ∉ box ι N) :
    (2 * Real.pi / P) ^ 2 * ((N : ℝ) + 1) ^ 2 ≤ HeatTorusFourier.frequencySquared P k := by
  classical
  have hk' : ∃ i, ¬ |k i| ≤ (N : ℤ) := by simpa only [mem_box, not_forall] using hk
  obtain ⟨i, hi⟩ := hk'
  have hnext : (N : ℤ) + 1 ≤ |k i| := by omega
  have hreal : (N : ℝ) + 1 ≤ |(k i : ℝ)| := by exact_mod_cast hnext
  unfold HeatTorusFourier.frequencySquared
  refine mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) hreal 2).trans ?_) (sq_nonneg _)
  rw [sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)

/-- The spatial Galerkin projections converge also on square-integrable
random fields, along any cofinal sequence of finite frequency sets. -/
theorem projectLp_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S : ℕ → Finset (ι → ℤ)} (hS : Tendsto S atTop atTop) (X : Lp Full 2 μ) :
    Tendsto (fun n => ((project (S n)).compLpL 2 μ) X) atTop (𝓝 X) := by
  let Y (n : ℕ) := ((project (S n)).compLpL 2 μ) X
  let e (n : ℕ) (ω : Ω) := ‖project (S n) (X ω) - X ω‖ ^ 2
  have he (n : ℕ) : ‖Y n - X‖ ^ 2 = ∫ ω, e n ω ∂μ := by
    rw [realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (Y n) X, (project (S n)).coeFn_compLpL X] with ω hs hp
    change (Y n - X) ω = (Y n ω) - X ω at hs
    rw [hs]
    exact congrArg (fun z : Full => ‖z - X ω‖ ^ 2) hp
  have hm (n : ℕ) : AEStronglyMeasurable (e n) μ :=
    (((project (S n)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable X)).sub
      (Lp.aestronglyMeasurable X)).norm.pow 2
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖e n ω‖ ≤ 4 * ‖X ω‖ ^ 2 := by
    apply Eventually.of_forall
    intro ω
    have hc := HeatTorusGalerkinProjection.projection_contraction (S n) (X ω)
    have hn : ‖project (S n) (X ω) - X ω‖ ≤ 2 * ‖X ω‖ := (norm_sub_le _ _).trans (by linarith)
    rw [show e n ω = ‖project (S n) (X ω) - X ω‖ ^ 2 from rfl, Real.norm_of_nonneg (sq_nonneg _)]
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by ring)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => e n ω) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro ω
    have hc := (((HeatTorusGalerkinProjection.project_tendsto (X ω)).comp hS).sub_const (X ω)).norm.pow 2
    simpa only [Function.comp_def, sub_self, norm_zero, e, zero_pow (by decide : 2 ≠ 0)] using hc
  have hint := tendsto_integral_of_dominated_convergence (fun ω => 4 * ‖X ω‖ ^ 2)
    hm ((Lp.memLp X).norm.integrable_sq.const_mul 4) hbound hlim
  have hsq : Tendsto (fun n => ‖Y n - X‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simp only [← he, integral_zero] at hint
    exact hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, Y] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

theorem box_projectLp_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (X : Lp Full 2 μ) :
    Tendsto (fun n => ((project (box ι n)).compLpL 2 μ) X) atTop (𝓝 X) :=
  projectLp_tendsto box_cofinal X

/-- For a square-integrable trajectory, its discarded Fourier modes
converge to zero in the integrated mean-square norm. -/
theorem box_tail_energy_tendsto_zero {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    {μ : Measure Ω} {ν : Measure T} (X : T → Lp Full 2 μ) (hX : MemLp X 2 ν) :
    Tendsto (fun n => ∫ t, ‖X t - ((project (box ι n)).compLpL 2 μ) (X t)‖ ^ 2 ∂ν)
      atTop (𝓝 0) := by
  let A (n : ℕ) := (project (box ι n)).compLpL 2 μ
  let e (n : ℕ) (t : T) := ‖X t - A n (X t)‖ ^ 2
  have hcontract (n : ℕ) (x : Lp Full 2 μ) : ‖A n x‖ ≤ ‖x‖ := by
    have h : ‖A n x‖ ≤ 1 * ‖x‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(project (box ι n)).coeFn_compLpL x] with ω hω
      change ‖A n x ω‖ ≤ 1 * ‖x ω‖
      rw [hω, one_mul]
      exact HeatTorusGalerkinProjection.projection_contraction (box ι n) (x ω)
    simpa only [one_mul] using h
  have hm (n : ℕ) : AEStronglyMeasurable (e n) ν :=
    (hX.aestronglyMeasurable.sub
      ((A n).continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)).norm.pow 2
  have hb (n : ℕ) : ∀ᵐ t ∂ν, ‖e n t‖ ≤ 4 * ‖X t‖ ^ 2 := by
    apply Eventually.of_forall
    intro t
    change ‖‖X t - A n (X t)‖ ^ 2‖ ≤ 4 * ‖X t‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := (norm_sub_le (X t) (A n (X t))).trans
      (add_le_add le_rfl (hcontract n (X t)))
    exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by ring)
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun n => e n t) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro t
    have h := ((tendsto_const_nhds (x := X t)).sub (box_projectLp_tendsto (X t))).norm.pow 2
    simpa only [e, A, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h
  simpa only [e, A, integral_zero] using
    tendsto_integral_of_dominated_convergence (fun t => 4 * ‖X t‖ ^ 2)
      hm (hX.norm.integrable_sq.const_mul 4) hb hlim

theorem box_heat_tail_le (N : ℕ) (P : ℝ) {t : ℝ} (ht : 0 ≤ t) (f : Full) :
    ‖HeatTorusFourier.heat P t f - project (box ι N) (HeatTorusFourier.heat P t f)‖ ≤
      Real.exp (-t * ((2 * Real.pi / P) ^ 2 * ((N : ℝ) + 1) ^ 2)) * ‖f‖ :=
  HeatTorusGalerkinProjection.heat_tail_le (box ι N) ht (fun _ hk => frequency_outside N P hk) f

end HeatTorusFrequencyExhaustion

#print axioms HeatTorusFrequencyExhaustion.box_cofinal
#print axioms HeatTorusFrequencyExhaustion.frequency_outside
#print axioms HeatTorusFrequencyExhaustion.projectLp_tendsto
#print axioms HeatTorusFrequencyExhaustion.box_projectLp_tendsto
#print axioms HeatTorusFrequencyExhaustion.box_tail_energy_tendsto_zero
#print axioms HeatTorusFrequencyExhaustion.box_heat_tail_le
