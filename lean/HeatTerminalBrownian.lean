import HeatTerminalNaturality
import SHE.RawCylindricalCoordinates

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatTerminalBrownian
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
  (b : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T)

local notation "ν" => (energyMeasure μ T).trim (predictable_le_product F)

local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

def e : HilbertBasis Unit ℝ (Space Unit ℝ) := ⟨LinearIsometryEquiv.refl ℝ _⟩

theorem unit_one : HeatUnitHilbertColumns.columnEquiv (1:ℝ) = e () := by
  apply lp.ext
  funext i
  cases i
  rw [HeatUnitHilbertColumns.column_apply, ← e.repr_symm_single ()]
  change 1 = (lp.single (E := fun _ : Unit => ℝ) 2 () (1:ℝ)) ()
  simp

theorem constant_projection (L : E →L[ℝ] ℝ) (g : E) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    HeatUnitHilbertLp.lpEquiv ν ((L.compLpL 2 ν) (RotatedCylindricalCoordinates.constant F μ T g)) =
      L g • RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) () := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply SHE.PastItoAlgebra.eq_of_ambient_ae
  have h1 := ae_eq_of_ae_eq_trim (HeatUnitHilbertLp.lpEquiv_ae ν
    ((L.compLpL 2 ν) (RotatedCylindricalCoordinates.constant F μ T g)))
  have h2 := ae_eq_of_ae_eq_trim (L.coeFn_compLpL (RotatedCylindricalCoordinates.constant F μ T g))
  have h3 := RotatedCylindricalCoordinates.constant_ae F μ T g
  have h4 := ae_eq_of_ae_eq_trim (Lp.coeFn_smul (L g)
    (RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) ()))
  have h5 := RotatedCylindricalCoordinates.constant_ae F μ T (e ())
  filter_upwards [h1,h2,h3,h4,h5] with p h1 h2 h3 h4 h5
  rw [h1,h2,h3,h4]
  change HeatUnitHilbertColumns.columnEquiv (L g) = L g • RotatedCylindricalCoordinates.constant F μ T (e ()) p
  rw [h5]
  have hh := (HeatUnitHilbertColumns.columnEquiv (E := ℝ)).map_smul (L g) (1:ℝ)
  simpa only [smul_eq_mul,mul_one,unit_one] using hh

theorem constant_integral (g : E) (t : ℝ≥0) :
    (HeatTerminalNaturality.integral F μ T b J).integral
      (StoppedItoInputs.stop F μ T t (RotatedCylindricalCoordinates.constant F μ T g)) =ᵐ[μ]
      (fun ω => J.integral (StoppedItoInputs.stop F μ T t
        (RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) ())) ω • g) := by
  have hz : (fun ω => (HeatTerminalNaturality.integral F μ T b J).integral
      (StoppedItoInputs.stop F μ T t (RotatedCylindricalCoordinates.constant F μ T g)) ω -
      J.integral (StoppedItoInputs.stop F μ T t
        (RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) ())) ω • g) =ᵐ[μ] (fun _ => (0:E)) := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    have he := HeatTerminalNaturality.scalar_commutes F μ T b J L
      (StoppedItoInputs.stop F μ T t (RotatedCylindricalCoordinates.constant F μ T g))
    have hmap : (L.compLpL 2 ν) (StoppedItoInputs.stop F μ T t (RotatedCylindricalCoordinates.constant F μ T g)) =
        StoppedItoInputs.stop F μ T t ((L.compLpL 2 ν) (RotatedCylindricalCoordinates.constant F μ T g)) := by
      apply SHE.PastItoAlgebra.eq_of_ambient_ae
      filter_upwards [ae_eq_of_ae_eq_trim (L.coeFn_compLpL (StoppedItoInputs.stop F μ T t (RotatedCylindricalCoordinates.constant F μ T g))),
        ae_eq_of_ae_eq_trim (L.coeFn_compLpL (RotatedCylindricalCoordinates.constant F μ T g)),
        StoppedItoInputs.stop_ae F μ T t (RotatedCylindricalCoordinates.constant F μ T g),
        StoppedItoInputs.stop_ae F μ T t ((L.compLpL 2 ν) (RotatedCylindricalCoordinates.constant F μ T g))] with p h1 h2 h3 h4
      rw [h1,h3,h4]
      by_cases hp : p ∈ StoppedItoInputs.before (t:ℝ)
      · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,h2]
      · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,map_zero]
    rw [hmap,HeatUnitHilbertStop.stop_lpEquiv,constant_projection F μ T L g,
      SHE.StoppedInputAlgebra.stop_smul,map_smul] at he
    have hp := L.coeFn_compLpL ((HeatTerminalNaturality.integral F μ T b J).integral
      (StoppedItoInputs.stop F μ T t (RotatedCylindricalCoordinates.constant F μ T g)))
    rw [he] at hp
    filter_upwards [hp,Lp.coeFn_smul (L g) (J.integral (StoppedItoInputs.stop F μ T t
      (RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) ())))] with ω hp hs
    change L (_ - _) = 0
    rw [map_sub,map_smul,←hp,hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

end HeatTerminalBrownian
#check @HeatTerminalBrownian.unit_one
#print axioms HeatTerminalBrownian.unit_one
#check @HeatTerminalBrownian.constant_projection
#print axioms HeatTerminalBrownian.constant_projection
#check @HeatTerminalBrownian.constant_integral
#print axioms HeatTerminalBrownian.constant_integral
