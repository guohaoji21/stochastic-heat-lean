import SHE.ProcessEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatL2PairingLimit
open MeasureTheory Filter SHE.PredictableL2
open scoped ENNReal Topology
variable {P E : Type*} [MeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ν : Measure P) [IsFiniteMeasure ν]

theorem integral_eq_inner (f g : P → E) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ p,inner ℝ (f p) (g p) ∂ν)=inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with p hf hg
  rw [hf,hg]

theorem tends (f : P → E) (hf : MemLp f 2 ν) (g : ℕ → P → E) (G : P → E)
    (hg : ∀ n, MemLp (g n) 2 ν) (hG : MemLp G 2 ν)
    (he : Tendsto (fun n => ∫ p,‖g n p-G p‖^2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,inner ℝ (f p) (g n p) ∂ν) atTop
      (𝓝 (∫ p,inner ℝ (f p) (G p) ∂ν)) := by
  let X := fun n => (hg n).toLp (g n)
  let Y := hG.toLp G
  have hsq (n : ℕ) : ‖X n-Y‖^2=(∫ p,‖g n p-G p‖^2 ∂ν) := by
    rw [realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (X n) Y,(hg n).coeFn_toLp,hG.coeFn_toLp] with p hs hx hy
    rw [hs]
    change ‖X n p-Y p‖^2=‖g n p-G p‖^2
    rw [hx,hy]
  have hs : Tendsto (fun n => ‖X n-Y‖^2) atTop (𝓝 0) :=
    he.congr' (Eventually.of_forall (fun n => (hsq n).symm))
  have hn : Tendsto (fun n => ‖X n-Y‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,abs_norm] using
      (Real.continuous_sqrt.tendsto 0).comp hs
  have hXY : Tendsto X atTop (𝓝 Y) := tendsto_iff_norm_sub_tendsto_zero.mpr hn
  have hF : Tendsto (fun _ : ℕ => hf.toLp f) atTop (𝓝 (hf.toLp f)) := tendsto_const_nhds
  have hh : Tendsto (fun n => inner ℝ (hf.toLp f) (X n)) atTop
      (𝓝 (inner ℝ (hf.toLp f) Y)) := hF.inner hXY
  have hraw := hh.congr' (Eventually.of_forall (fun n => (integral_eq_inner ν f (g n) hf (hg n)).symm))
  rw [←integral_eq_inner ν f G hf hG] at hraw
  exact hraw

end HeatL2PairingLimit
#check @HeatL2PairingLimit.integral_eq_inner
#print axioms HeatL2PairingLimit.integral_eq_inner
#check @HeatL2PairingLimit.tends
#print HeatL2PairingLimit.tends
#print axioms HeatL2PairingLimit.tends
