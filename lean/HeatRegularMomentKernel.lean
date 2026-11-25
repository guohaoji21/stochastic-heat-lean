import HeatRegularKernel
import SHE.TimeCausalSplit

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace HeatRegularMomentKernel
open MeasureTheory Set Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

theorem mass_bound (H : ℝ≥0) {γ : ℝ} (hγ : 0<γ) {t : ℝ≥0} (ht : t≤H) :
    (∫⁻ s, HeatRegularKernel.kernel γ ((t:ℝ)-(s:ℝ)) ∂timeMeasure H) ≤
      ENNReal.ofReal (HeatRegularKernel.mass γ) := by
  rw [causal_lintegral_of_zero ht]
  · rw [timeMeasure_lintegral]
    calc
      _ = ∫⁻ r in Ioc (0:ℝ) t, HeatRegularKernel.kernel γ ((t:ℝ)-r) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        rw [Real.coe_toNNReal _ hr.1.le]
      _ ≤ ∫⁻ r : ℝ, HeatRegularKernel.kernel γ ((t:ℝ)-r) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ r : ℝ, HeatRegularKernel.kernel γ r := by rw [lintegral_sub_left_eq_self]
      _ = _ := HeatRegularKernel.kernel_mass γ hγ
  · intro s hs
    unfold HeatRegularKernel.kernel
    exact indicator_of_notMem (fun hm => (not_lt_of_ge
      (sub_nonpos.mpr (by exact_mod_cast hs.le))) hm) _

theorem mass_tends_zero : Tendsto HeatRegularKernel.mass atTop (𝓝 0) := by
  have hh := tendsto_inv_atTop_zero.const_mul (1/2:ℝ)
  simp only [mul_zero] at hh
  convert hh using 1
  funext γ
  simp only [HeatRegularKernel.mass,div_eq_mul_inv,mul_inv_rev]
  ring

end HeatRegularMomentKernel
#check @HeatRegularMomentKernel.mass_bound
#print axioms HeatRegularMomentKernel.mass_bound
#check @HeatRegularMomentKernel.mass_tends_zero
#print axioms HeatRegularMomentKernel.mass_tends_zero
