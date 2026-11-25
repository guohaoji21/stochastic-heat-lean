import SHE.HilbertColumns
import SHE.StoppedInputParameter
import SHEStochastic.L2HilbertSum

set_option autoImplicit false
noncomputable section
namespace HeatUnitHilbertColumns
open SHE.HilbertColumns
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def column : E →ₗᵢ[ℝ] Space Unit E where
  toLinearMap := lp.lsingle (𝕜 := ℝ) (E := fun _ : Unit => E) 2 ()
  norm_map' x := by
    simpa using (lp.norm_single (E := fun _ : Unit => E) (p := (2 : ENNReal))
      (by norm_num : (0 : ENNReal) < 2) () x)

theorem column_surjective : Function.Surjective (column (E := E)) := by
  intro v
  refine ⟨v (), ?_⟩
  ext i
  cases i
  simp [column]

def columnEquiv : E ≃ₗᵢ[ℝ] Space Unit E :=
  LinearIsometryEquiv.ofSurjective (column (E := E)) column_surjective

theorem column_apply (x : E) : columnEquiv x () = x := by
  simp [columnEquiv, column]

theorem inner_column (x y : E) :
    inner ℝ (columnEquiv x) (columnEquiv y) = inner ℝ x y :=
  columnEquiv.inner_map_map x y

end HeatUnitHilbertColumns
#check @HeatUnitHilbertColumns.column_surjective
#print axioms HeatUnitHilbertColumns.column_surjective
#check @HeatUnitHilbertColumns.column_apply
#print axioms HeatUnitHilbertColumns.column_apply
#check @HeatUnitHilbertColumns.inner_column
#print axioms HeatUnitHilbertColumns.inner_column

namespace HeatUnitHilbertLp
open MeasureTheory SHE.HilbertColumns SHEStochastic.L2HilbertSum
open scoped ENNReal
variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ν : Measure α)

theorem lift_surjective : Function.Surjective (lift ν (HeatUnitHilbertColumns.column (E := E))) := by
  intro g
  let L := (HeatUnitHilbertColumns.columnEquiv (E := E)).symm.toLinearIsometry.toContinuousLinearMap
  let f : Lp E 2 ν := L.compLpL 2 ν g
  refine ⟨f, ?_⟩
  apply Lp.ext
  filter_upwards [lift_ae ν (HeatUnitHilbertColumns.column (E := E)) f,
    L.coeFn_compLpL g] with x hx hy
  change _ = g x
  rw [hx]
  change HeatUnitHilbertColumns.columnEquiv (f x) = g x
  change f x = _ at hy
  rw [hy]
  change HeatUnitHilbertColumns.columnEquiv ((HeatUnitHilbertColumns.columnEquiv (E := E)).symm (g x)) = g x
  exact (HeatUnitHilbertColumns.columnEquiv (E := E)).apply_symm_apply (g x)

def lpEquiv : Lp E 2 ν ≃ₗᵢ[ℝ] Lp (Space Unit E) 2 ν :=
  LinearIsometryEquiv.ofSurjective (lift ν (HeatUnitHilbertColumns.column (E := E))) (lift_surjective ν)

theorem lpEquiv_ae (f : Lp E 2 ν) :
    lpEquiv ν f =ᵐ[ν] fun x => HeatUnitHilbertColumns.columnEquiv (f x) :=
  lift_ae ν (HeatUnitHilbertColumns.column (E := E)) f

end HeatUnitHilbertLp
#check @HeatUnitHilbertLp.lift_surjective
#print axioms HeatUnitHilbertLp.lift_surjective
#check @HeatUnitHilbertLp.lpEquiv_ae
#print axioms HeatUnitHilbertLp.lpEquiv_ae

namespace HeatUnitHilbertStop
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (T : ℝ≥0)

theorem stop_lpEquiv (t : ℝ) (u : Process (E := E) F μ T) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    let ν := (energyMeasure μ T).trim (predictable_le_product F)
    HeatUnitHilbertLp.lpEquiv ν (stop F μ T t u) =
      stop F μ T t (HeatUnitHilbertLp.lpEquiv ν u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let ν := (energyMeasure μ T).trim (predictable_le_product F)
  apply Lp.ext
  filter_upwards [HeatUnitHilbertLp.lpEquiv_ae ν (stop F μ T t u),
    HeatUnitHilbertLp.lpEquiv_ae ν u,
    SHE.StoppedInputParameter.stop_ae_trim F μ T u t,
    SHE.StoppedInputParameter.stop_ae_trim F μ T (HeatUnitHilbertLp.lpEquiv ν u) t]
    with p hleft hu hstop hright
  rw [hleft, hright, hstop]
  by_cases hp : p ∈ before (Ω := Ω) t
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, hu]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, map_zero]

end HeatUnitHilbertStop
#check @HeatUnitHilbertStop.stop_lpEquiv
#print axioms HeatUnitHilbertStop.stop_lpEquiv

namespace HeatUnitHilbertStop
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)

theorem cross_integral_eq (a c : ℝ≥0) (u v : Process (E := E) F μ T) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    let ν := (energyMeasure μ T).trim (predictable_le_product F)
    ∀ᵐ ω ∂μ,
      (∫ t in Set.Ioc a c, inner ℝ ((HeatUnitHilbertLp.lpEquiv ν u) (t, ω))
        ((HeatUnitHilbertLp.lpEquiv ν v) (t, ω)) ∂SHE.PredictableL2.timeMeasure T) =
      ∫ t in Set.Ioc a c, inner ℝ (u (t, ω)) (v (t, ω)) ∂SHE.PredictableL2.timeMeasure T := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let ν := (energyMeasure μ T).trim (predictable_le_product F)
  have hu := ae_eq_of_ae_eq_trim (HeatUnitHilbertLp.lpEquiv_ae ν u)
  have hv := ae_eq_of_ae_eq_trim (HeatUnitHilbertLp.lpEquiv_ae ν v)
  letI : MeasurableSpace (ℝ≥0 × Ω) :=
    (inferInstance : MeasurableSpace ℝ≥0).prod (inferInstance : MeasurableSpace Ω)
  have hsu := (Measure.measurePreserving_swap (μ := μ)
    (ν := SHE.PredictableL2.timeMeasure T)).quasiMeasurePreserving.ae hu
  have hsv := (Measure.measurePreserving_swap (μ := μ)
    (ν := SHE.PredictableL2.timeMeasure T)).quasiMeasurePreserving.ae hv
  filter_upwards [Measure.ae_ae_of_ae_prod hsu, Measure.ae_ae_of_ae_prod hsv] with ω hu hv
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hu, ae_restrict_of_ae hv] with t hu hv
  dsimp only [Prod.swap] at hu hv
  rw [hu, hv, HeatUnitHilbertColumns.inner_column]

end HeatUnitHilbertStop
#check @HeatUnitHilbertStop.cross_integral_eq
#print axioms HeatUnitHilbertStop.cross_integral_eq
