import HeatTerminalNaturality

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatLpSpatialExt
open MeasureTheory Filter
open scoped ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω)

theorem ext (X Y : Lp E 2 μ)
    (h : ∀ φ : E, ((innerSL ℝ φ).compLpL 2 μ) X=((innerSL ℝ φ).compLpL 2 μ) Y) : X=Y := by
  have hz : (fun ω => X ω-Y ω)=ᵐ[μ] fun _ => (0:E) := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    let φ := (InnerProductSpace.toDual ℝ E).symm L
    have he : innerSL ℝ φ=L := (InnerProductSpace.toDual ℝ E).apply_symm_apply L
    have hh := h φ
    rw [he] at hh
    filter_upwards [L.coeFn_compLpL X,L.coeFn_compLpL Y] with ω hx hy
    change L (X ω-Y ω)=0
    rw [map_sub,←hx,←hy,hh,sub_self]
  apply Lp.ext
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

theorem scalar_comp (A : E →L[ℝ] E) (hA : ∀ x y, inner ℝ (A x) y=inner ℝ x (A y)) (φ : E) :
    innerSL ℝ (A φ)=(innerSL ℝ φ).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  exact hA φ x

theorem scalar_compLp (A : E →L[ℝ] E) (hA : ∀ x y, inner ℝ (A x) y=inner ℝ x (A y))
    (φ : E) (X : Lp E 2 μ) :
    ((innerSL ℝ (A φ)).compLpL 2 μ) X=((innerSL ℝ φ).compLpL 2 μ) ((A.compLpL 2 μ) X) := by
  rw [scalar_comp A hA φ]
  exact (HeatTerminalNaturality.compLp_comp μ (innerSL ℝ φ) A X).symm

end HeatLpSpatialExt
#check @HeatLpSpatialExt.ext
#print axioms HeatLpSpatialExt.ext
#check @HeatLpSpatialExt.scalar_comp
#print axioms HeatLpSpatialExt.scalar_comp
#check @HeatLpSpatialExt.scalar_compLp
#print HeatLpSpatialExt.scalar_compLp
#print axioms HeatLpSpatialExt.scalar_compLp
