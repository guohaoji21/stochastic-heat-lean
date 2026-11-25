import HeatPredictableStateInput
import SHE.KernelItoModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatVolterraKernel
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.ApproximationClock SHE.ApproximationCells
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

def endTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 := Real.toNNReal (right n t)

theorem endTime_eq_point (n : ℕ) (t : ℝ≥0) : endTime n t = point n (index n t) := by
  unfold endTime
  rw [right_eq_point, Real.toNNReal_coe]

theorem endTime_measurable (n : ℕ) : Measurable (endTime n) :=
  (continuous_real_toNNReal.measurable.comp (right_measurable n)).comp measurable_coe_nnreal_real

theorem endTime_ge (n : ℕ) (t : ℝ≥0) : t ≤ endTime n t := by
  exact_mod_cast (right_bounds n t.property).1.trans (Real.le_coe_toNNReal _)

theorem endTime_tendsto (t : ℝ≥0) : Tendsto (fun n => endTime n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  convert (right_tendsto t.property) using 1
  funext n
  unfold endTime
  exact Real.coe_toNNReal _ (t.property.trans (right_bounds n t.property).1)
  all_goals rfl

theorem left_lt_time (n : ℕ) (t : ℝ≥0) : left n t < (t : ℝ) := by
  have h := (right_bounds n t.property).2
  change right n (t:ℝ)-delta n < (t:ℝ)
  exact sub_lt_iff_lt_add.mpr h

variable (S : ℝ≥0 → E →L[ℝ] E) (M : E →L[ℝ] E)

def raw (u : ℝ≥0 × Ω → E) (p : ℝ≥0 × (ℝ≥0 × Ω)) : E :=
  if p.2.1 < p.1 then S (p.1-p.2.1) (M (u p.2)) else 0

def approx (u : ℝ≥0 × Ω → E) (n : ℕ) (p : ℝ≥0 × (ℝ≥0 × Ω)) : E :=
  if (p.2.1 : ℝ) < left n p.1 then S (endTime n p.1-p.2.1) (M (u p.2)) else 0

variable (hS : ∀ x, Continuous (fun t => S t x)) (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)
include hS hcontr

theorem raw_measurable (u : ℝ≥0 × Ω → E) (hu : Measurable u) : Measurable (raw S M u) := by
  unfold raw
  apply Measurable.ite (measurableSet_lt measurable_snd.fst measurable_fst)
  · exact (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
      ((measurable_fst.sub measurable_snd.fst).prodMk (M.continuous.measurable.comp (hu.comp measurable_snd)))
  · exact measurable_const

theorem approx_measurable (u : ℝ≥0 × Ω → E) (hu : Measurable u) (n : ℕ) : Measurable (approx S M u n) := by
  unfold approx
  apply Measurable.ite (measurableSet_lt (measurable_coe_nnreal_real.comp measurable_snd.fst)
    ((left_measurable n).comp (measurable_coe_nnreal_real.comp measurable_fst)))
  · exact (HeatPredictableSemigroup.continuous_action S hS hcontr).measurable.comp
      (((endTime_measurable n).comp measurable_fst |>.sub measurable_snd.fst).prodMk
        (M.continuous.measurable.comp (hu.comp measurable_snd)))
  · exact measurable_const

theorem approx_tendsto (u : ℝ≥0 × Ω → E) (p : ℝ≥0 × (ℝ≥0 × Ω)) :
    Tendsto (fun n => approx S M u n p) atTop (𝓝 (raw S M u p)) := by
  by_cases hst : p.2.1 < p.1
  · have hstR : (p.2.1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hst
    have he := (tendsto_order.mp (left_tendsto p.1.property)).1 _ hstR
    have hs : Tendsto (fun n => S (endTime n p.1-p.2.1) (M (u p.2))) atTop
        (𝓝 (S (p.1-p.2.1) (M (u p.2)))) :=
      (hS _).continuousAt.tendsto.comp ((endTime_tendsto p.1).sub_const _)
    simp only [raw, if_pos hst]
    apply hs.congr'
    filter_upwards [he] with n hn
    simp only [approx]
    split_ifs with hcase
    · rfl
    · exact False.elim (hcase hn)
  · have hle : (p.1 : ℝ) ≤ (p.2.1 : ℝ) := by exact_mod_cast le_of_not_gt hst
    have he : ∀ n, ¬ (p.2.1 : ℝ) < left n p.1 := fun n => not_lt.mpr ((left_lt_time n p.1).le.trans hle)
    simpa only [approx, raw, if_neg hst, if_neg (he _)] using (tendsto_const_nhds (x := (0 : E)))

theorem approx_norm_le (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    (u : ℝ≥0 × Ω → E) (n : ℕ) (p : ℝ≥0 × (ℝ≥0 × Ω)) :
    ‖approx S M u n p‖ ≤ ‖raw S M u p‖ := by
  by_cases h : (p.2.1 : ℝ) < left n p.1
  · have hst : p.2.1 < p.1 := by exact_mod_cast h.trans (left_lt_time n p.1)
    have hte := endTime_ge n p.1
    have ht : (endTime n p.1-p.1)+(p.1-p.2.1) = endTime n p.1-p.2.1 :=
      tsub_add_tsub_cancel hte hst.le
    simp only [approx, if_pos h, raw, if_pos hst]
    rw [← ht, hsem, ContinuousLinearMap.comp_apply]
    exact hcontr _ _
  · simp only [approx, if_neg h, norm_zero]
    exact norm_nonneg _

end HeatVolterraKernel
#check @HeatVolterraKernel.endTime_eq_point
#print axioms HeatVolterraKernel.endTime_eq_point
#check @HeatVolterraKernel.endTime_measurable
#print axioms HeatVolterraKernel.endTime_measurable
#check @HeatVolterraKernel.endTime_ge
#print axioms HeatVolterraKernel.endTime_ge
#check @HeatVolterraKernel.endTime_tendsto
#print axioms HeatVolterraKernel.endTime_tendsto
#check @HeatVolterraKernel.left_lt_time
#print axioms HeatVolterraKernel.left_lt_time
#check @HeatVolterraKernel.raw_measurable
#print axioms HeatVolterraKernel.raw_measurable
#check @HeatVolterraKernel.approx_measurable
#print axioms HeatVolterraKernel.approx_measurable
#check @HeatVolterraKernel.approx_tendsto
#print axioms HeatVolterraKernel.approx_tendsto
#check @HeatVolterraKernel.approx_norm_le
#print axioms HeatVolterraKernel.approx_norm_le
