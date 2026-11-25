import HeatTerminalTransport
import HeatHilbertLocality

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatTerminalNaturality
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

section Lp
variable {P E V W : Type*} [MeasurableSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem compLp_comp (ν : Measure P) (L : V →L[ℝ] W) (A : E →L[ℝ] V) (u : Lp E 2 ν) :
    (L.compLpL 2 ν) ((A.compLpL 2 ν) u) = ((L.comp A).compLpL 2 ν) u := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL ((A.compLpL 2 ν) u), A.coeFn_compLpL u,
    (L.comp A).coeFn_compLpL u] with p h1 h2 h3
  rw [h1,h2,h3]
  rfl
end Lp

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
  (b : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T)

local notation "ν" => (energyMeasure μ T).trim (predictable_le_product F)

def integral : StandardTerminalIto (C := E) (E := E) F μ T :=
  HeatTerminalTransport.fromUnitColumns F μ T (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J)

theorem unit_projection (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ T) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    ((mapCLM L).compLpL 2 ν) (HeatUnitHilbertLp.lpEquiv ν u) =
      HeatUnitHilbertLp.lpEquiv ν ((L.compLpL 2 ν) u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  filter_upwards [(mapCLM L).coeFn_compLpL (HeatUnitHilbertLp.lpEquiv ν u),
    HeatUnitHilbertLp.lpEquiv_ae ν u, L.coeFn_compLpL u,
    HeatUnitHilbertLp.lpEquiv_ae ν ((L.compLpL 2 ν) u)] with p h1 h2 h3 h4
  rw [h1,h2,h4,h3]
  apply lp.ext
  funext i
  cases i
  simp only [mapCLM_apply, HeatUnitHilbertColumns.column_apply]

theorem scalar_commutes (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ T) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    (L.compLpL 2 μ) ((integral F μ T b J).integral u) =
      J.integral (HeatUnitHilbertLp.lpEquiv ν ((L.compLpL 2 ν) u)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change (L.compLpL 2 μ) (SHEStochastic.HilbertTerminalIto.integral F μ T b J
    (HeatUnitHilbertLp.lpEquiv ν u)) = _
  rw [SHEStochastic.HilbertTerminalIto.commutes, unit_projection F μ T L u]

theorem commutes (A : E →L[ℝ] E) (u : Process (E := E) F μ T) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    (A.compLpL 2 μ) ((integral F μ T b J).integral u) =
      (integral F μ T b J).integral ((A.compLpL 2 ν) u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let I := integral F μ T b J
  have hz : (fun ω => (A.compLpL 2 μ) (I.integral u) ω - I.integral ((A.compLpL 2 ν) u) ω)
      =ᵐ[μ] (fun _ => (0:E)) := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    have he : (L.compLpL 2 μ) ((A.compLpL 2 μ) (I.integral u)) =
        (L.compLpL 2 μ) (I.integral ((A.compLpL 2 ν) u)) := by
      rw [compLp_comp, scalar_commutes, scalar_commutes, compLp_comp]
    filter_upwards [L.coeFn_compLpL ((A.compLpL 2 μ) (I.integral u)),
      L.coeFn_compLpL (I.integral ((A.compLpL 2 ν) u))] with ω h1 h2
    change L (_ - _) = 0
    rw [map_sub, ← h1, ← h2, he, sub_self]
  apply Lp.ext
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω


theorem unit_map (u : Process (E := E) F μ T) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    HeatUnitHilbertLp.lpEquiv ν u =
      ((HeatUnitHilbertColumns.columnEquiv (E := E)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 ν) u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  exact (HeatUnitHilbertLp.lpEquiv_ae ν u).trans
    ((HeatUnitHilbertColumns.columnEquiv (E := E)).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL u).symm

theorem locality (hlocal : StandardTerminalPastLocality J) :
    StandardTerminalPastLocality (integral F μ T b J) := by
  letI : MeasurableSpace (Space Unit E) := borel _
  letI : BorelSpace (Space Unit E) := ⟨rfl⟩
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let V := HeatUnitHilbertLp.lpEquiv (E := E) ν
  let L := (HeatUnitHilbertColumns.columnEquiv (E := E)).toContinuousLinearEquiv.toContinuousLinearMap
  have he (u : Process (E := E) F μ T) : V u = (L.compLpL 2 ν) u := unit_map F μ T u
  intro a A hA u
  have hh := HeatHilbertLocality.locality F μ T b J hlocal a A hA (V u)
  have hp : V (PastItoInputs.post F μ T a u) = PastItoInputs.post F μ T a (V u) := by
    rw [he,he,SHE.ItoLocalityTransport.post_map]
  have ha : V (PastItoInputs.eventProcess F μ T a A hA u) =
      PastItoInputs.eventProcess F μ T a A hA (V u) := by
    rw [he,he,SHE.ItoLocalityTransport.event_map]
  rw [←hp,←ha] at hh
  exact hh

end HeatTerminalNaturality
#check @HeatTerminalNaturality.compLp_comp
#print axioms HeatTerminalNaturality.compLp_comp
#check @HeatTerminalNaturality.unit_projection
#print axioms HeatTerminalNaturality.unit_projection
#check @HeatTerminalNaturality.scalar_commutes
#print axioms HeatTerminalNaturality.scalar_commutes
#check @HeatTerminalNaturality.commutes
#print axioms HeatTerminalNaturality.commutes

#check @HeatTerminalNaturality.unit_map
#print axioms HeatTerminalNaturality.unit_map
#check @HeatTerminalNaturality.locality
#print axioms HeatTerminalNaturality.locality
