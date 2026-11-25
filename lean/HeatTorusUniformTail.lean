import HeatRegularKernel
import HeatTorusFrequencyExhaustion
import HeatTorusProjectedConvolution

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace HeatTorusUniformTail

open Filter MeasureTheory
open UnitAddTorus HeatTorusProjectedConvolution HeatTorusFrequencyExhaustion
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local notation "Full" => HeatTorusFourier.State ι

def rate (P : ℝ) (n : ℕ) : ℝ := (2 * Real.pi / P) ^ 2 * ((n : ℝ) + 1) ^ 2

theorem mass_tendsto_zero {P : ℝ} (hP : 0 < P) :
    Tendsto (fun n => HeatRegularKernel.mass (rate P n)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop := by
    simpa only [pow_two] using h.atTop_mul_atTop₀ h
  have hr : Tendsto (fun n => 2 * rate P n) atTop atTop := by
    have he : (fun n => 2 * rate P n) =
        fun n : ℕ => (2 * (2 * Real.pi / P) ^ 2) * ((n : ℝ) + 1) ^ 2 := by
      funext n
      unfold rate
      ring
    rw [he]
    exact h'.const_mul_atTop (by positivity)
  simpa only [HeatRegularKernel.mass, one_div, Function.comp_def] using
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hr

def tail (n : ℕ) : Full →L[ℝ] Full :=
  ContinuousLinearMap.id ℝ Full - ((HeatTorusGalerkinProjection.project (box ι n)).restrictScalars ℝ)

theorem heat_decay (P : ℝ) (n : ℕ) (t : ℝ≥0) (x : Full) :
    ‖tail n (fullHeat P t x)‖ ≤ Real.exp (-rate P n * (t : ℝ)) * ‖x‖ := by
  have h := box_heat_tail_le n P t.property x
  change ‖tail n (fullHeat P t x)‖ ≤ Real.exp (-(t : ℝ) * rate P n) * ‖x‖ at h
  rw [show -(t : ℝ) * rate P n = -rate P n * (t : ℝ) by ring] at h
  exact h

theorem rate_pos {P : ℝ} (hP : 0 < P) (n : ℕ) : 0 < rate P n := by
  unfold rate
  positivity

end HeatTorusUniformTail

#print axioms HeatTorusUniformTail.heat_decay
#print axioms HeatTorusUniformTail.mass_tendsto_zero
