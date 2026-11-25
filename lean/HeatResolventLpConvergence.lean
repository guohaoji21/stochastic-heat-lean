import HeatResolventApproximation
import HeatVolterraSlice

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatResolventLpConvergence
open MeasureTheory Filter HeatIntervalNormalization HeatDirichletResolvent HeatResolventApproximation
open scoped Topology ENNReal
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

theorem tendsto (u : Lp Base 2 ν) :
    Tendsto (fun n => ((approx n).compLpL 2 ν) u) atTop (𝓝 u) := by
  apply HeatVolterraSlice.dominated_Lp_convergence ν _ u u
  · intro n
    filter_upwards [(approx n).coeFn_compLpL u] with x hx
    rw [hx]
    exact smoothing_contraction (a := (n:ℝ)+1) (by have hn := Nat.cast_nonneg (α := ℝ) n;linarith) _
  · filter_upwards [ae_all_iff.mpr (fun n => (approx n).coeFn_compLpL u)] with x hx
    have he : (fun n => ((approx n).compLpL 2 ν) u x)=(fun n => approx n (u x)) := funext hx
    rw [he]
    exact tendsto_identity (u x)

end HeatResolventLpConvergence
#check @HeatResolventLpConvergence.tendsto
#print HeatResolventLpConvergence.tendsto
#print axioms HeatResolventLpConvergence.tendsto
