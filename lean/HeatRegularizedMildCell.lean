import HeatRegularizedCell
import HeatRegularizedKernelCross
import HeatActualCellEnergy
import HeatLiftedAlgebra

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatRegularizedMildCell
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem identity (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (hlocal : StandardTerminalPastLocality J)
    {a b : ℝ≥0} (hab : a≤b) (ε : ℝ≥0) (hε : b-a≤ε)
    (Ya Yb za zb U : Lp E 2 μ) (u v : Process (E := E) F μ H)
    (hYa : AEStronglyMeasurable[F a] Ya μ) (hza : AEStronglyMeasurable[F a] za μ)
    (hy : Yb=((S (b-a)).compLpL 2 μ) Ya+U+
      (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u))
    (hz : za=((S (b-a)).compLpL 2 μ) zb+HeatActualCellEnergy.drift F μ H S hS hcontr M a b v-
      (I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v)) :
    inner ℝ Yb (((S ε).compLpL 2 μ) zb)-inner ℝ Ya (((S ε).compLpL 2 μ) za)=
      inner ℝ U (((S ε).compLpL 2 μ) zb)-
      inner ℝ (((S ε).compLpL 2 μ) Ya) (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v)-
      inner ℝ (((S (ε-(b-a))).compLpL 2 μ)
        ((I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u)))
        (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v)+
      (∫ p, (Set.Ioc a b).indicator (fun s => inner ℝ (M (u (s,p.2))) (S ε (v (s,p.2)))) p.1 ∂energyMeasure μ H) := by
  let A := HeatLiftedSemigroup.family μ S (b-a)
  let B := HeatLiftedSemigroup.family μ S ε
  let C := HeatLiftedSemigroup.family μ S (ε-(b-a))
  let D := HeatActualCellEnergy.drift F μ H S hS hcontr M a b v
  let N := (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u)
  let P := (I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v)
  have hA := HeatLiftedAlgebra.symmetric μ S hsym (b-a)
  have hB := HeatLiftedAlgebra.symmetric μ S hsym ε
  have hC := HeatLiftedAlgebra.symmetric μ S hsym (ε-(b-a))
  have hAB : A.comp B=B.comp A := by
    rw [←HeatLiftedAlgebra.semigroup μ S hsem,←HeatLiftedAlgebra.semigroup μ S hsem,add_comm]
  have hBC : B=C.comp A := by
    have hh := HeatLiftedAlgebra.semigroup μ S hsem (ε-(b-a)) (b-a)
    rw [tsub_add_cancel_of_le hε] at hh
    exact hh
  have hmap (L : E →L[ℝ] E) (X : Lp E 2 μ) (hx : AEStronglyMeasurable[F a] X μ) :
      AEStronglyMeasurable[F a] ((L.compLpL 2 μ) X) μ :=
    (L.continuous.comp_aestronglyMeasurable hx).congr (L.coeFn_compLpL X).symm
  have hl := HeatTerminalNaturality.locality F μ H basis J hlocal
  have horth1 : inner ℝ (B Ya) P=0 := by
    have hh := HeatPastPairing.future_orthogonal I hl a
      (StoppedItoInputs.stop F μ H b (HeatBackwardKernel.factor F μ H S hS hcontr
        (ContinuousLinearMap.id ℝ E) a v)) (B Ya) (hmap (S ε) Ya hYa)
    calc
      _ = inner ℝ P (B Ya) := real_inner_comm _ _
      _ = 0 := hh
  have horth2 : inner ℝ (C N) za=0 := by
    have hh := HeatPastPairing.future_orthogonal I hl a
      (StoppedItoInputs.stop F μ H b (HeatPredictableStateInput.factor F μ H S hS hcontr M b u))
      (C za) (hmap (S (ε-(b-a))) za hza)
    exact (hC N za).trans hh
  have he := HeatRegularizedCell.identity A B C hA hB hC hAB hBC Ya Yb za zb U D N P hy hz horth1 horth2
  have hcross := HeatRegularizedKernelCross.ito_cross F μ H S hS hcontr M basis J hsem hsym hab (ε-(b-a)) u v
  rw [tsub_add_cancel_of_le hε] at hcross
  change inner ℝ (C N) P=_ at hcross
  rw [hcross] at he
  exact he

end HeatRegularizedMildCell
#check @HeatRegularizedMildCell.identity
#print HeatRegularizedMildCell.identity
#print axioms HeatRegularizedMildCell.identity
