import HeatTerminalNaturality
import SHEStochastic.NativeStoppedInputComparison

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatHilbertRandomStop
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

def project (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) : Process (E := Space Unit ℝ) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact HeatUnitHilbertLp.lpEquiv ν ((L.compLpL 2 ν) u)

theorem project_ae (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) :
    project F μ H L u=ᵐ[energyMeasure μ H] fun p => HeatUnitHilbertColumns.columnEquiv (L (u p)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  filter_upwards [ae_eq_of_ae_eq_trim (HeatUnitHilbertLp.lpEquiv_ae ν ((L.compLpL 2 ν) u)),
    ae_eq_of_ae_eq_trim (L.coeFn_compLpL u)] with p hp hL
  change HeatUnitHilbertLp.lpEquiv ν ((L.compLpL 2 ν) u) p=_
  rw [hp,hL]

theorem project_stop (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) (T : ℝ≥0) :
    project F μ H L (StoppedItoInputs.stop F μ H T u)=
      StoppedItoInputs.stop F μ H T (project F μ H L u) := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [project_ae F μ H L (StoppedItoInputs.stop F μ H T u),
    StoppedItoInputs.stop_ae F μ H T u,StoppedItoInputs.stop_ae F μ H T (project F μ H L u),
    project_ae F μ H L u] with p hp hs ht hpu
  rw [hp,hs,ht]
  by_cases hpt : p∈StoppedItoInputs.before (T:ℝ)
  · rw [Set.indicator_of_mem hpt,Set.indicator_of_mem hpt,hpu]
  · rw [Set.indicator_of_notMem hpt,Set.indicator_of_notMem hpt,map_zero,map_zero]

theorem integral_projection (L : E →L[ℝ] ℝ) (u : Process (E := E) F μ H) :
    (fun ω => L ((I).integral u ω))=ᵐ[μ] J.integral (project F μ H L u) := by
  have hh := L.coeFn_compLpL ((I).integral u)
  rw [HeatTerminalNaturality.scalar_commutes] at hh
  exact hh.symm

theorem integral_eq_before (hlocal : StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u v : Process (E := E) F μ H) (T : ℝ≥0)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (huv : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 → u p=v p) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0)≤τ ω →
      (I).integral (StoppedItoInputs.stop F μ H T u) ω=
        (I).integral (StoppedItoInputs.stop F μ H T v) ω := by
  have hcoord (i : κ) : ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0)≤τ ω →
      inner ℝ (basis i) ((I).integral (StoppedItoInputs.stop F μ H T u) ω)=
        inner ℝ (basis i) ((I).integral (StoppedItoInputs.stop F μ H T v) ω) := by
    let L := innerSL ℝ (basis i)
    have hproj : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 →
        project F μ H L u p=project F μ H L v p := by
      filter_upwards [huv,project_ae F μ H L u,project_ae F μ H L v] with p hp hu hv hτp
      rw [hu,hv,hp hτp]
    have he := SHEStochastic.NativeStoppedInputComparison.integral_eq_before F μ H J hlocal hversions hnull
      (project F μ H L u) (project F μ H L v) T τ hτ hproj
    rw [←project_stop F μ H L u T,←project_stop F μ H L v T] at he
    filter_upwards [he,integral_projection F μ H basis J L (StoppedItoInputs.stop F μ H T u),
      integral_projection F μ H basis J L (StoppedItoInputs.stop F μ H T v)] with ω he hu hv hτT
    exact hu.trans ((he hτT).trans hv.symm)
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω hτT
  apply basis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply]
  exact hω i hτT

end HeatHilbertRandomStop
#check @HeatHilbertRandomStop.project_ae
#print axioms HeatHilbertRandomStop.project_ae
#check @HeatHilbertRandomStop.project_stop
#print axioms HeatHilbertRandomStop.project_stop
#check @HeatHilbertRandomStop.integral_projection
#print axioms HeatHilbertRandomStop.integral_projection
#check @HeatHilbertRandomStop.integral_eq_before
#print HeatHilbertRandomStop.integral_eq_before
#print axioms HeatHilbertRandomStop.integral_eq_before
