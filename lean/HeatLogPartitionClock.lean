import HeatLogClock

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatLogPartitionClock
open Filter Finset
open scoped BigOperators

def ell (L : ℝ) : ℕ → ℝ
  | 0 => L
  | n+1 => ell L n+Real.log (2*ell L n)/4

theorem one_le (L : ℝ) (hL : 1≤L) : ∀ n,1≤ell L n := by
  intro n
  induction n with
  | zero => exact hL
  | succ n ih =>
    have hp : 0<Real.log (2*ell L n) := Real.log_pos (by linarith)
    simp only [ell]
    linarith

theorem recurrence (L : ℝ) (n : ℕ) :
    4*(ell L (n+1)-ell L n)=Real.log (2*ell L n) := by
  simp only [ell]
  ring

theorem lower_linear (L : ℝ) (hL : 1≤L) :
    ∀ n : ℕ,L+(n:ℝ)*(Real.log 2/4)≤ell L n := by
  intro n
  induction n with
  | zero => simp [ell]
  | succ n ih =>
    have he := Real.log_le_log (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤2*ell L n by have := one_le L hL n;linarith)
    simp only [ell,Nat.cast_add,Nat.cast_one]
    linarith

theorem tends_top (L : ℝ) (hL : 1≤L) : Tendsto (ell L) atTop atTop := by
  have hp : 0<Real.log 2/4 := by have := Real.log_pos (by norm_num : (1:ℝ)<2);positivity
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => L+(n:ℝ)*(Real.log 2/4)) atTop atTop :=
    tendsto_atTop_add_const_left _ L (hn.atTop_mul_const hp)
  exact tendsto_atTop_mono (lower_linear L hL) hh

theorem reciprocal_sum_lower (L : ℝ) (hL : 1≤L) : ∀ n,
    4*(Real.log (Real.log (2*ell L n))-Real.log (Real.log (2*L)))≤
      ∑ k∈range n,(ell L k)⁻¹ := by
  intro n
  induction n with
  | zero => simp [ell]
  | succ n ih =>
    have he := HeatLogClock.loglog_step (ell L n) (ell L (n+1))
      (one_le L hL n) (recurrence L n)
    rw [sum_range_succ]
    linarith

theorem reciprocal_sum_tends_top (L : ℝ) (hL : 1≤L) :
    Tendsto (fun n => ∑ k∈range n,(ell L k)⁻¹) atTop atTop := by
  have he := tends_top L hL
  have h2 : Tendsto (fun n => 2*ell L n) atTop atTop := he.const_mul_atTop (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h2)
  have hh : Tendsto (fun n => 4*(Real.log (Real.log (2*ell L n))-Real.log (Real.log (2*L)))) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-Real.log (Real.log (2*L))) hlog).const_mul_atTop (by norm_num)
  exact tendsto_atTop_mono (reciprocal_sum_lower L hL) hh

end HeatLogPartitionClock
#check @HeatLogPartitionClock.one_le
#print axioms HeatLogPartitionClock.one_le
#check @HeatLogPartitionClock.recurrence
#print axioms HeatLogPartitionClock.recurrence
#check @HeatLogPartitionClock.lower_linear
#print axioms HeatLogPartitionClock.lower_linear
#check @HeatLogPartitionClock.tends_top
#print axioms HeatLogPartitionClock.tends_top
#check @HeatLogPartitionClock.reciprocal_sum_lower
#print axioms HeatLogPartitionClock.reciprocal_sum_lower
#check @HeatLogPartitionClock.reciprocal_sum_tends_top
#print axioms HeatLogPartitionClock.reciprocal_sum_tends_top
