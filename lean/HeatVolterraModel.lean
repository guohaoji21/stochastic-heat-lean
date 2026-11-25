import HeatVolterraKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import SHE.StoppedItoInputs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatVolterraModel
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.ApproximationCells SHE.KernelItoLimit
open HeatVolterraKernel
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
include hS hcontr

local instance : SFinite (energyMeasure μ H) := by
  unfold energyMeasure
  infer_instance

theorem state_measurable (u : Process (E := E) F μ H) : Measurable (fun p : ℝ≥0 × Ω => u p) :=
  ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable

theorem raw_norm_bound (u : Process (E := E) F μ H) (p : ℝ≥0 × (ℝ≥0 × Ω)) :
    ‖raw S M u p‖ ≤ ‖M‖*‖u p.2‖ := by
  unfold raw
  split_ifs
  · exact (hcontr _ _).trans (M.le_opNorm _)
  · rw [norm_zero]
    positivity

theorem raw_memLp (u : Process (E := E) F μ H) :
    MemLp (raw S M u) 2 (SHE.HaarKernelL2Approximation.measure μ H) := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hb := (hu.norm.const_mul ‖M‖).comp_snd (timeMeasure H)
  apply hb.mono' (raw_measurable S M hS hcontr u (state_measurable F μ H S hS hcontr u)).aestronglyMeasurable
  filter_upwards [] with p
  exact raw_norm_bound F μ H S hS hcontr M u p

theorem raw_energy_finite (u : Process (E := E) F μ H) :
    (∫⁻ p, ENNReal.ofReal (‖raw S M u p‖^2) ∂SHE.HaarKernelL2Approximation.measure μ H) < ∞ := by
  have hf := raw_memLp F μ H S hS hcontr M u
  apply lt_top_iff_ne_top.mpr
  apply (lintegral_ofReal_ne_top_iff_integrable (hf.aestronglyMeasurable.norm.pow 2)
    (Filter.Eventually.of_forall fun p => sq_nonneg ‖raw S M u p‖)).mpr
  exact hf.norm.integrable_sq

def input (u : Process (E := E) F μ H) (n k : ℕ) : Process (E := E) F μ H :=
  StoppedItoInputs.stop F μ H (point n (k-1))
    (HeatPredictableStateInput.factor F μ H S hS hcontr M (point n k) u)

theorem input_stopped (u : Process (E := E) F μ H) (n k : ℕ) :
    ∀ᵐ p ∂energyMeasure μ H, point n (k-1) < p.1 → input F μ H S hS hcontr M u n k p = 0 :=
  StoppedItoInputs.stop_stopped F μ H _ _

theorem input_at (u : Process (E := E) F μ H) (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    input F μ H S hS hcontr M u n (index n t) =ᵐ[energyMeasure μ H]
      (fun p => approx S M u n (t,p)) := by
  have hs := StoppedItoInputs.stop_ae F μ H (point n (index n t-1))
    (HeatPredictableStateInput.factor F μ H S hS hcontr M (point n (index n t)) u)
  have hf := HeatPredictableStateInput.factor_ae F μ H S hS hcontr M (point n (index n t)) u
  filter_upwards [hs,hf] with p hstop hfactor
  change StoppedItoInputs.stop F μ H _ _ p = _
  rw [hstop]
  unfold approx
  rw [endTime_eq_point, SHE.ApproximationCells.left_eq_point n ht]
  by_cases h : (p.1 : ℝ) < (point n (index n t-1) : ℝ)
  · rw [Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (point n (index n t-1):ℝ) from h), if_pos h, hfactor]
  · rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (point n (index n t-1):ℝ) from h), if_neg h]

def model (hsem : ∀ s t, S (s+t) = (S s).comp (S t)) :
    Model (Process (E := E) F μ H) E F μ H where
  raw u := raw S M u
  approx u := approx S M u
  raw_measurable u := raw_measurable S M hS hcontr u (state_measurable F μ H S hS hcontr u)
  approx_measurable u n := approx_measurable S M hS hcontr u (state_measurable F μ H S hS hcontr u) n
  raw_energy_finite := raw_energy_finite F μ H S hS hcontr M
  approx_tendsto u := Filter.Eventually.of_forall (approx_tendsto S M hS hcontr u)
  approx_norm_le u n := Filter.Eventually.of_forall (approx_norm_le S M hS hcontr hsem u n)
  input := input F μ H S hS hcontr M
  input_stopped := input_stopped F μ H S hS hcontr M
  input_at u n t ht _ := input_at F μ H S hS hcontr M u n t ht

end HeatVolterraModel
#check @HeatVolterraModel.state_measurable
#print axioms HeatVolterraModel.state_measurable
#check @HeatVolterraModel.raw_norm_bound
#print axioms HeatVolterraModel.raw_norm_bound
#check @HeatVolterraModel.raw_memLp
#print axioms HeatVolterraModel.raw_memLp
#check @HeatVolterraModel.raw_energy_finite
#print axioms HeatVolterraModel.raw_energy_finite
#check @HeatVolterraModel.input_stopped
#print axioms HeatVolterraModel.input_stopped
#check @HeatVolterraModel.input_at
#print axioms HeatVolterraModel.input_at
