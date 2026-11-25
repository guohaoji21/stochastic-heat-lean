import HeatMildSolution

set_option autoImplicit false
noncomputable section
namespace HeatScalarLpConst
open MeasureTheory Filter
open scoped ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem map_const (L : E →L[ℝ] ℝ) (x : E) :
    (L.compLpL 2 μ) (Lp.const 2 μ x)=Lp.const 2 μ (L x) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (Lp.const 2 μ x),Lp.coeFn_const 2 μ x,Lp.coeFn_const 2 μ (L x)] with ω hm hx hy
  rw [hm,hx,hy]
  rfl

end HeatScalarLpConst
#check @HeatScalarLpConst.map_const
#print HeatScalarLpConst.map_const
#print axioms HeatScalarLpConst.map_const
