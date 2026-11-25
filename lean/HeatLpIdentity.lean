import HeatLiftedSemigroup

set_option autoImplicit false
noncomputable section
namespace HeatLpIdentity
open MeasureTheory
open scoped ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure Ω)

theorem add (A : E →L[ℝ] E) (X Y U N : Lp E 2 μ)
    (h : X=ᵐ[μ] fun ω => A (Y ω)+U ω+N ω) : X=(A.compLpL 2 μ) Y+U+N := by
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_add (((A.compLpL 2 μ) Y)+U) N,
    Lp.coeFn_add ((A.compLpL 2 μ) Y) U,A.coeFn_compLpL Y] with ω hh h1 h2 ha
  rw [h1]
  change X ω=(((A.compLpL 2 μ) Y)+U) ω+N ω
  rw [h2]
  change X ω=((A.compLpL 2 μ) Y) ω+U ω+N ω
  rw [ha]
  exact hh

theorem sub (A : E →L[ℝ] E) (X Y U N : Lp E 2 μ)
    (h : X=ᵐ[μ] fun ω => A (Y ω)+U ω-N ω) : X=(A.compLpL 2 μ) Y+U-N := by
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_sub (((A.compLpL 2 μ) Y)+U) N,
    Lp.coeFn_add ((A.compLpL 2 μ) Y) U,A.coeFn_compLpL Y] with ω hh h1 h2 ha
  rw [h1]
  change X ω=(((A.compLpL 2 μ) Y)+U) ω-N ω
  rw [h2]
  change X ω=((A.compLpL 2 μ) Y) ω+U ω-N ω
  rw [ha]
  exact hh

end HeatLpIdentity
#check @HeatLpIdentity.add
#print axioms HeatLpIdentity.add
#check @HeatLpIdentity.sub
#print axioms HeatLpIdentity.sub
