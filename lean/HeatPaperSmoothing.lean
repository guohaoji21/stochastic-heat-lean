import HeatIntervalNormalization
import SHE.HeatTimeSmoothing

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatPaperSmoothing
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation HeatIntervalNormalization
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

theorem real_bound {τ δ θ : ℝ} (hτ : 0<τ) (hδ : 0≤δ) (hθ : 0≤θ) (hθ1 : θ≤1)
    (v : RealL2) :
    ‖RealHeat.realHeat δ (RealHeat.realHeat τ v)-RealHeat.realHeat τ v‖≤(δ/τ)^θ*‖v‖ := by
  rw [←realEmbed_norm_eq (RealHeat.realHeat δ (RealHeat.realHeat τ v)-RealHeat.realHeat τ v),
    map_sub,RealHeat.realEmbed_realHeat,RealHeat.realEmbed_realHeat]
  exact (HeatTimeSmoothing.heat_increment_bound hτ hδ hθ hθ1 (realEmbed v)).trans_eq
    (by rw [realEmbed_norm_eq])

theorem paper_bound {τ δ θ : ℝ} (hτ : 0<τ) (hδ : 0≤δ) (hθ : 0≤θ) (hθ1 : θ≤1)
    (v : Base) : ‖paperHeat δ (paperHeat τ v)-paperHeat τ v‖≤(δ/τ)^θ*‖v‖ := by
  rw [←paperOddEquiv.norm_map (paperHeat δ (paperHeat τ v)-paperHeat τ v),map_sub]
  simp only [paperHeat_apply,LinearIsometryEquiv.apply_symm_apply]
  change ‖RealHeat.realHeat (δ/400) (RealHeat.realHeat (τ/400) (paperOddEquiv v : RealL2))-
    RealHeat.realHeat (τ/400) (paperOddEquiv v : RealL2)‖≤_
  have he : (δ/400)/(τ/400)=δ/τ := by ring
  have hh := real_bound (τ := τ/400) (δ := δ/400) (div_pos hτ (by norm_num)) (div_nonneg hδ (by norm_num)) hθ hθ1
    (paperOddEquiv v : RealL2)
  rw [he] at hh
  exact hh.trans_eq (by rw [show ‖(paperOddEquiv v : RealL2)‖=‖paperOddEquiv v‖ from rfl,paperOddEquiv.norm_map])

end HeatPaperSmoothing
#check @HeatPaperSmoothing.real_bound
#print axioms HeatPaperSmoothing.real_bound
#check @HeatPaperSmoothing.paper_bound
#print axioms HeatPaperSmoothing.paper_bound
