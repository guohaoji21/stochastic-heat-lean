import HeatLiftedSemigroup
import HeatMildCellPairing
import HeatTerminalNaturality

set_option autoImplicit false
noncomputable section
namespace HeatLiftedAlgebra
open MeasureTheory
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (S : ℝ≥0 → E →L[ℝ] E)

theorem zero (hzero : S 0=ContinuousLinearMap.id ℝ E) :
    HeatLiftedSemigroup.family μ S 0=ContinuousLinearMap.id ℝ (Lp E 2 μ) := by
  apply ContinuousLinearMap.ext
  intro X
  apply Lp.ext
  filter_upwards [(S 0).coeFn_compLpL X] with ω hω
  change ((S 0).compLpL 2 μ) X ω=X ω
  rw [hω,hzero]
  rfl

theorem semigroup (hsem : ∀ s t, S (s+t)=(S s).comp (S t)) (s t : ℝ≥0) :
    HeatLiftedSemigroup.family μ S (s+t)=
      (HeatLiftedSemigroup.family μ S s).comp (HeatLiftedSemigroup.family μ S t) := by
  apply ContinuousLinearMap.ext
  intro X
  dsimp only [HeatLiftedSemigroup.family,ContinuousLinearMap.comp_apply]
  rw [hsem]
  exact (HeatTerminalNaturality.compLp_comp μ (S s) (S t) X).symm

theorem symmetric (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (t : ℝ≥0) (X Y : Lp E 2 μ) :
    inner ℝ (HeatLiftedSemigroup.family μ S t X) Y=
      inner ℝ X (HeatLiftedSemigroup.family μ S t Y) :=
  HeatMildCellPairing.lifted_self_adjoint μ (S t) (hsym t) X Y

end HeatLiftedAlgebra
#check @HeatLiftedAlgebra.zero
#print axioms HeatLiftedAlgebra.zero
#check @HeatLiftedAlgebra.semigroup
#print axioms HeatLiftedAlgebra.semigroup
#check @HeatLiftedAlgebra.symmetric
#print axioms HeatLiftedAlgebra.symmetric
