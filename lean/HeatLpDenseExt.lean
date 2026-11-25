import HeatLpSpatialExt
import HeatDirichletH01Core

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatLpDenseExt
open MeasureTheory Filter
open scoped ENNReal
variable {Ω E D : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace D] (μ : Measure Ω)

theorem ext (d : D → E) (hd : DenseRange d) (X Y : Lp E 2 μ)
    (h : ∀ a, ((innerSL ℝ (d a)).compLpL 2 μ) X=((innerSL ℝ (d a)).compLpL 2 μ) Y) : X=Y := by
  apply HeatLpSpatialExt.ext μ X Y
  intro φ
  refine hd.induction_on (p := fun φ : E => ((innerSL ℝ φ).compLpL 2 μ) X=((innerSL ℝ φ).compLpL 2 μ) Y) φ ?_ h
  exact isClosed_eq (((innerSL ℝ).compLpL₂ 2 μ).flip X).continuous
    (((innerSL ℝ).compLpL₂ 2 μ).flip Y).continuous

end HeatLpDenseExt
namespace HeatLpVectorConst
open MeasureTheory
open scoped ENNReal
variable {Ω E D : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem map_const (L : E →L[ℝ] D) (x : E) :
    (L.compLpL 2 μ) (Lp.const 2 μ x)=Lp.const 2 μ (L x) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (Lp.const 2 μ x),Lp.coeFn_const 2 μ x,Lp.coeFn_const 2 μ (L x)] with ω hm hx hy
  rw [hm,hx,hy]
  rfl

end HeatLpVectorConst
#check @HeatLpDenseExt.ext
#print axioms HeatLpDenseExt.ext
#check @HeatLpVectorConst.map_const
#print HeatLpVectorConst.map_const
#print axioms HeatLpVectorConst.map_const
