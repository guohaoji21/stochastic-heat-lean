import HeatVolterraModel
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatVolterraSlice
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatVolterraKernel
open scoped NNReal ENNReal Topology

section Domination
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] (ν : Measure X) [IsFiniteMeasure ν]

theorem dominated_Lp_convergence (v : ℕ → Lp E 2 ν) (f g : Lp E 2 ν)
    (hb : ∀ n, ∀ᵐ x ∂ν, ‖v n x‖ ≤ ‖g x‖)
    (hl : ∀ᵐ x ∂ν, Tendsto (fun n => v n x) atTop (𝓝 (f x))) :
    Tendsto v atTop (𝓝 f) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' v f).mpr
  have hui : UnifIntegrable (fun n x => v n x) 2 ν := by
    apply (unifIntegrable_const (by norm_num : (1:ℝ≥0∞) ≤ 2) (by norm_num) (Lp.memLp g)).ae_mono
      (fun n => Lp.aestronglyMeasurable (v n))
    intro n
    filter_upwards [hb n] with x hx
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    exact hx
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => Lp.aestronglyMeasurable (v n)) (Lp.memLp f) hui hl
end Domination

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
include hS hcontr

local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance

def slice (t : ℝ≥0) (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  StoppedItoInputs.stop F μ H t (HeatPredictableStateInput.factor F μ H S hS hcontr M t u)

theorem slice_ae (t : ℝ≥0) (u : Process (E := E) F μ H) :
    slice F μ H S hS hcontr M t u =ᵐ[energyMeasure μ H] (fun p => raw S M u (t,p)) := by
  have hs := StoppedItoInputs.stop_ae F μ H t (HeatPredictableStateInput.factor F μ H S hS hcontr M t u)
  have hf := HeatPredictableStateInput.factor_ae F μ H S hS hcontr M t u
  filter_upwards [hs,hf] with p hstop hfactor
  change StoppedItoInputs.stop F μ H _ _ p = _
  rw [hstop]
  by_cases h : p.1 < t
  · rw [Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (t:ℝ) from h), hfactor]
    simp only [raw, if_pos h]
  · rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (t:ℝ) from h)]
    simp only [raw, if_neg h]

theorem raw_sequence_tendsto (u : ℝ≥0 × Ω → E) (a : ℕ → ℝ≥0) (t : ℝ≥0)
    (ha : Tendsto a atTop (𝓝 t)) (s : ℝ≥0) (ω : Ω) (hne : s ≠ t) :
    Tendsto (fun n => raw S M u (a n,(s,ω))) atTop (𝓝 (raw S M u (t,(s,ω)))) := by
  by_cases hst : s < t
  · have he := (tendsto_order.mp ha).1 s hst
    have hl := (hS (M (u (s,ω)))).continuousAt.tendsto.comp (ha.sub_const s)
    simp only [raw, if_pos hst]
    apply hl.congr'
    filter_upwards [he] with n hn
    split_ifs with hcase
    · rfl
  · have hts : t < s := lt_of_le_of_ne (le_of_not_gt hst) hne.symm
    have he := (tendsto_order.mp ha).2 s hts
    simp only [raw, if_neg hst]
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    split_ifs with hcase
    · exact False.elim ((not_lt_of_ge hn.le) hcase)
    · rfl

theorem approximation_input_tendsto (u : Process (E := E) F μ H) (t : ℝ≥0) (ht : 0 < t)
    (hsem : ∀ s t, S (s+t) = (S s).comp (S t)) :
    Tendsto (fun n => HeatVolterraModel.input F μ H S hS hcontr M u n (SHE.ApproximationCells.index n t))
      atTop (𝓝 (slice F μ H S hS hcontr M t u)) := by
  let A := ambientIsometry (E := E) (energyMeasure μ H) (predictable_le_product F)
  let v : ℕ → Lp E 2 (energyMeasure μ H) := fun n =>
    A (HeatVolterraModel.input F μ H S hS hcontr M u n (SHE.ApproximationCells.index n t))
  let f : Lp E 2 (energyMeasure μ H) := A (slice F μ H S hS hcontr M t u)
  let g : Lp E 2 (energyMeasure μ H) := ‖M‖ • A u
  have hV : ∀ n, (v n : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] (fun p => approx S M u n (t,p)) := by
    intro n
    exact (ambient_ae _ _ _).trans (HeatVolterraModel.input_at F μ H S hS hcontr M u n t ht)
  have hf : (f : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] (fun p => raw S M u (t,p)) :=
    (ambient_ae _ _ _).trans (slice_ae F μ H S hS hcontr M t u)
  have hg : (g : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] (fun p => ‖M‖ • u p) := by
    filter_upwards [Lp.coeFn_smul ‖M‖ (A u), ambient_ae _ _ u] with p hs hu
    rw [hs]
    change ‖M‖ • (A u p) = ‖M‖ • u p
    exact congrArg (fun z : E => ‖M‖ • z) hu
  have hvlim : Tendsto v atTop (𝓝 f) := by
    apply dominated_Lp_convergence _ v f g
    · intro n
      filter_upwards [hV n,hg] with p hn hgg
      rw [hn,hgg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg M)]
      exact (approx_norm_le S M hS hcontr hsem u n (t,p)).trans
        (HeatVolterraModel.raw_norm_bound F μ H S hS hcontr M u (t,p))
    · filter_upwards [ae_all_iff.mpr hV,hf] with p hp hpf
      have hl := approx_tendsto S M hS hcontr u (t,p)
      simpa only [← hp, ← hpf] using hl
  exact A.isometry.tendsto_nhds_iff.mpr hvlim

end HeatVolterraSlice
#check @HeatVolterraSlice.dominated_Lp_convergence
#print axioms HeatVolterraSlice.dominated_Lp_convergence
#check @HeatVolterraSlice.slice_ae
#print axioms HeatVolterraSlice.slice_ae
#check @HeatVolterraSlice.raw_sequence_tendsto
#print axioms HeatVolterraSlice.raw_sequence_tendsto
#check @HeatVolterraSlice.approximation_input_tendsto
#print axioms HeatVolterraSlice.approximation_input_tendsto
