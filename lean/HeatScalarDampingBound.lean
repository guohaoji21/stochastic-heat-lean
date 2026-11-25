import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatScalarDampingBound
open Set MeasureTheory Real
open scoped Topology

theorem primitive_upper {X X' : ℝ → ℝ} {c B T t : ℝ} (hc : 0<c) (hB : 0≤B)
    (hX : ContinuousOn X (Icc 0 T))
    (hd : ∀ r∈Ico 0 T, HasDerivWithinAt X (X' r) (Ici r) r)
    (h0 : X 0=0) (hb : ∀ r∈Ico 0 T, X' r≤ -c*X r+B) (ht : t∈Icc 0 T) : c*X t≤B := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le hX
    (fun r hr q hq => (hd r hr).liminf_right_slope_le hq) (by simp [h0] : X 0≤(0:ℝ)) hb t ht
  rw [sub_zero,gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hc.ne')] at hg
  dsimp only at hg
  simp only [zero_mul,zero_add] at hg
  have hm := mul_le_mul_of_nonneg_left hg hc.le
  have he : c*(B/(-c)*(exp (-c*t)-1))=B*(1-exp (-c*t)) := by field_simp;ring
  rw [he] at hm
  nlinarith [mul_nonneg hB (exp_pos (-c*t)).le]

theorem bound {x F : ℝ → ℝ} {c B T : ℝ} (hc : 0≤c) (hB : 0≤B)
    (hx : Continuous x) (hF : ∀ t∈Icc 0 T, |F t|≤B)
    (heq : ∀ t∈Icc 0 T, x t+c*(∫ r in (0:ℝ)..t,x r)=F t) :
    ∀ t∈Icc 0 T, |x t|≤2*B := by
  by_cases hz : c=0
  · subst c
    intro t ht
    have h := heq t ht
    simp only [zero_mul,add_zero] at h
    rw [h]
    linarith [hF t ht]
  have hcp : 0<c := lt_of_le_of_ne hc (Ne.symm hz)
  let X : ℝ → ℝ := fun t => ∫ r in (0:ℝ)..t,x r
  have hX : Continuous X := by
    exact intervalIntegral.continuous_primitive (μ := (volume : Measure ℝ)) (fun a b => hx.intervalIntegrable a b) 0
  have hd (r : ℝ) : HasDerivAt X (x r) r := by
    exact intervalIntegral.integral_hasDerivAt_right (hx.intervalIntegrable _ _) (hx.stronglyMeasurableAtFilter volume (𝓝 r)) hx.continuousAt
  intro t ht
  have hu := primitive_upper (t := t) hcp hB hX.continuousOn
    (fun r _ => (hd r).hasDerivWithinAt) (by simp [X])
    (fun r hr => by have he := heq r ⟨hr.1,hr.2.le⟩;have hf := (abs_le.mp (hF r ⟨hr.1,hr.2.le⟩)).2;dsimp [X] at *;linarith)
  have hl := primitive_upper (t := t) hcp hB hX.neg.continuousOn
    (fun r _ => (hd r).neg.hasDerivWithinAt) (by simp [X])
    (fun r hr => by have he := heq r ⟨hr.1,hr.2.le⟩;have hf := (abs_le.mp (hF r ⟨hr.1,hr.2.le⟩)).1;dsimp [X] at *;linarith)
  have h₁ := hu ht
  have h₂ := hl ht
  have he := heq t ht
  have hf := abs_le.mp (hF t ht)
  apply abs_le.mpr
  dsimp [X] at h₁ h₂
  constructor <;> linarith

end HeatScalarDampingBound
#check @HeatScalarDampingBound.primitive_upper
#print axioms HeatScalarDampingBound.primitive_upper
#check @HeatScalarDampingBound.bound
#print HeatScalarDampingBound.bound
#print axioms HeatScalarDampingBound.bound
