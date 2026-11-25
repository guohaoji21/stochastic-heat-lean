import HeatFourierFrameMeasure
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatFourierFrameConvergence
open MeasureTheory Filter HeatIntervalNormalization HeatFourierFrame
open scoped Topology

theorem tendsto (u : ℕ → Base) (v g : Base)
    (hlim : ∀ k : ℤ, Tendsto (fun n => coordinate k (u n)) atTop (𝓝 (coordinate k v)))
    (hb : ∀ n k, |coordinate k (u n-v)|≤2*|coordinate k g|) :
    Tendsto u atTop (𝓝 v) := by
  have hs := (HeatFourierFrameMeasure.summable g).mul_left 4
  have hl (k : ℤ) : Tendsto (fun n => (coordinate k (u n-v))^2) atTop (𝓝 (0:ℝ)) := by
    have hh := ((hlim k).sub_const (coordinate k v)).pow 2
    simpa only [map_sub,sub_self,zero_pow (by norm_num : (2:ℕ)≠0)] using hh
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ k : ℤ, ‖(coordinate k (u n-v))^2‖≤4*(coordinate k g)^2 := by
    apply Eventually.of_forall
    intro n k
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hb n k) 2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_pow,sq_abs,show (2:ℝ)^2=4 by norm_num] using hh
  have ht := tendsto_tsum_of_dominated_convergence hs hl hbound
  have hn : Tendsto (fun n => ‖u n-v‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [←parseval,tsum_zero] using ht
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hnorm

theorem nonnegative_limit (u : ℕ → Base) (v : Base) (hu : Tendsto u atTop (𝓝 v))
    (hp : ∀ n,∀ᵐ x ∂baseMeasure,0≤u n x) : ∀ᵐ x ∂baseMeasure,0≤v x := by
  have hc := tendstoInMeasure_of_tendsto_Lp hu
  obtain ⟨σ,hσ,hae⟩ := hc.exists_seq_tendsto_ae
  filter_upwards [hae,ae_all_iff.mpr hp] with x hx hn
  exact ge_of_tendsto hx (Eventually.of_forall (fun n => hn (σ n)))

end HeatFourierFrameConvergence
#check @HeatFourierFrameConvergence.tendsto
#print axioms HeatFourierFrameConvergence.tendsto
#check @HeatFourierFrameConvergence.nonnegative_limit
#print HeatFourierFrameConvergence.nonnegative_limit
#print axioms HeatFourierFrameConvergence.nonnegative_limit
