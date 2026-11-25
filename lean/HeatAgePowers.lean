import HeatPaperSmoothing

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatAgePowers

theorem fresh {r H : ℝ} (hr : 0<r) (hrH : r≤H) :
    1≤H^(1/2:ℝ)*r^(-(1/2:ℝ)) := by
  have h := Real.rpow_le_rpow hr.le hrH (by norm_num : (0:ℝ)≤1/2)
  calc
    (1:ℝ) = r^(1/2:ℝ)*r^(-(1/2:ℝ)) := by rw [←Real.rpow_add hr];norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hr.le _)

theorem old {δ r H : ℝ} (hδ : 0≤δ) (hδH : δ≤H) (hr : 0<r) :
    ((δ/r)^(3/8:ℝ))^2≤H^(1/2:ℝ)*δ^(1/4:ℝ)*r^(-(3/4:ℝ)) := by
  have hd : δ^(3/4:ℝ)≤H^(1/2:ℝ)*δ^(1/4:ℝ) := by
    rw [show (3/4:ℝ)=1/2+1/4 by norm_num,Real.rpow_add' hδ (by norm_num)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hδ hδH (by norm_num)) (Real.rpow_nonneg hδ _)
  rw [←Real.rpow_mul_natCast (div_nonneg hδ hr.le)]
  norm_num only [Nat.cast_ofNat,show (3/8:ℝ)*2=3/4 by norm_num]
  rw [Real.div_rpow hδ hr.le,div_eq_mul_inv,←Real.rpow_neg hr.le]
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hr.le _)

end HeatAgePowers
#check @HeatAgePowers.fresh
#print axioms HeatAgePowers.fresh
#check @HeatAgePowers.old
#print axioms HeatAgePowers.old
