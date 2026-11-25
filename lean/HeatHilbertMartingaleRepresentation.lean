import HeatTerminalNaturality
import HeatStoppedMartingale
import SHEStochastic.ColumnsHilbertSum
import SHEStochastic.FiniteItoStoppedVersions

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatHilbertMartingaleRepresentation

open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns SHEStochastic
open scoped NNReal ENNReal

local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

variable {Ω κ E : Type*} [mΩ : MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private theorem coordinate {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (b : HilbertBasis κ ℝ E) (x : Lp E 2 μ) (i : κ) :
    (L2HilbertSum.total μ _ (ColumnsHilbertSum.unit_total b)).linearIsometryEquiv x i =
      ((innerSL ℝ (b i)).compLpL 2 μ) x := by
  rw [L2HilbertSum.coordinate, L2HilbertSum.lift_adjoint μ (ColumnsHilbertSum.unit b) i,
    ColumnsHilbertSum.unit_adjoint]

/-- A scalar martingale representation lifts to the same Itô integral
on a Hilbert space with a countable orthonormal basis. -/
theorem centered_representation (F : Filtration ℝ≥0 mΩ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
    (b : HilbertBasis κ ℝ E) (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T)
    (hscalar : ∀ x : Lp ℝ 2 μ, AEStronglyMeasurable[F T] (x : Ω → ℝ) μ →
      (∫ ω, x ω ∂μ) = 0 →
      x ∈ LinearMap.range J.integral.toLinearMap)
    (X : Lp E 2 μ) (hX : AEStronglyMeasurable[F T] (X : Ω → E) μ)
    (hc : ∫ ω, X ω ∂μ = 0) :
    ∃ v : Process (E := E) F μ T, (HeatTerminalNaturality.integral F μ T b J).integral v = X := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let ν := (energyMeasure μ T).trim (predictable_le_product F)
  let L (i : κ) := innerSL ℝ (b i)
  let D := (L2HilbertSum.total μ _ (ColumnsHilbertSum.unit_total b)).linearIsometryEquiv
  let S := (L2HilbertSum.total ν _ (ColumnsHilbertSum.unit_total b)).linearIsometryEquiv
  have hD (i : κ) : (D X) i = ((L i).compLpL 2 μ) X := coordinate μ b X i
  have hcomp (i : κ) : ((L i).compLpL 2 μ) X =ᵐ[μ] fun ω => L i (X ω) :=
    (L i).coeFn_compLpL X
  have hXi (i : κ) : AEStronglyMeasurable[F T] (D X i : Ω → ℝ) μ := by
    rw [hD]
    exact ((L i).continuous.comp_aestronglyMeasurable hX).congr (hcomp i).symm
  have hci (i : κ) : ∫ ω, D X i ω ∂μ = 0 := by
    rw [hD, integral_congr_ae (hcomp i), (L i).integral_comp_comm ((Lp.memLp X).integrable one_le_two),
      hc, map_zero]
  have hrepr (i : κ) : ∃ w : Process (E := Space Unit ℝ) F μ T, J.integral w = D X i :=
    hscalar (D X i) (hXi i) (hci i)
  choose w hw using hrepr
  let U := HeatUnitHilbertLp.lpEquiv (E := ℝ) ν
  let u (i : κ) := U.symm (w i)
  have hu (i : κ) : ‖u i‖ = ‖D X i‖ := by
    rw [← hw i, J.integral.norm_map]
    exact U.symm.norm_map _
  let a : lp (fun _ : κ => Lp ℝ 2 ν) 2 := ⟨u, memℓp_gen (by
    simpa only [hu] using (lp.memℓp (D X)).summable (by norm_num : 0 < (2 : ENNReal).toReal))⟩
  let v := S.symm a
  refine ⟨v, D.injective ?_⟩
  apply lp.ext
  funext i
  change D _ i = D X i
  have hv : ((L i).compLpL 2 ν) v = u i := by
    rw [← coordinate ν b v i]
    change (S (S.symm a)) i = u i
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [show D ((HeatTerminalNaturality.integral F μ T b J).integral v) i =
    ((L i).compLpL 2 μ) ((HeatTerminalNaturality.integral F μ T b J).integral v)
    from coordinate μ b _ i, HeatTerminalNaturality.scalar_commutes, hv]
  change J.integral (U (U.symm (w i))) = D X i
  rw [LinearIsometryEquiv.apply_symm_apply, hw]

/-- A single predictable integrand represents the conditional expectations of
a terminal value at every time. The deterministic term is its mean. -/
theorem conditional_representation (F : Filtration ℝ≥0 mΩ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
    (I : StandardTerminalIto (C := E) (E := E) F μ T) (hI : StandardTerminalPastLocality I)
    (hrep : ∀ x : Lp E 2 μ, AEStronglyMeasurable[F T] (x : Ω → E) μ →
      (∫ ω, x ω ∂μ) = 0 → x ∈ LinearMap.range I.integral.toLinearMap)
    (X : Lp E 2 μ) (hX : AEStronglyMeasurable[F T] (X : Ω → E) μ) :
    ∃ u : Process (E := E) F μ T,
      ∀ t : ℝ≥0, t ≤ T → μ[(X : Ω → E) | F t] =ᵐ[μ]
        fun ω => (∫ z, X z ∂μ) + I.integral (StoppedItoInputs.stop F μ T t u) ω := by
  let c := ∫ ω, X ω ∂μ
  let C₀ := Lp.const 2 μ c
  let Y := X - C₀
  have hY : (Y : Ω → E) =ᵐ[μ] (fun ω => X ω - c) := by
    filter_upwards [Lp.coeFn_sub X C₀, Lp.coeFn_const 2 μ c] with ω hsub hc
    exact hsub.trans (congrArg (fun x => X ω - x) hc)
  have hcenter : ∫ ω, Y ω ∂μ = 0 := by
    rw [integral_congr_ae hY, integral_sub ((Lp.memLp X).integrable one_le_two) (integrable_const c),
      integral_const]
    simp [c]
  have hYa : AEStronglyMeasurable[F T] (Y : Ω → E) μ :=
    (hX.sub stronglyMeasurable_const.aestronglyMeasurable).congr hY.symm
  have hu' : ∃ u : Process (E := E) F μ T, I.integral u = Y := hrep Y hYa hcenter
  obtain ⟨u, hu⟩ := hu'
  refine ⟨u, fun t ht => ?_⟩
  let W := fun s : ℝ≥0 => I.integral (StoppedItoInputs.stop F μ T s u)
  have hW : W T = Y := by
    dsimp only [W]
    rw [SHEStochastic.FiniteItoStoppedVersions.stop_horizon, hu]
  have hXsum : (X : Ω → E) =ᵐ[μ] (fun ω => c + W T ω) := by
    filter_upwards [hY] with ω hω
    rw [hW, hω]
    abel
  have hs := (condExp_congr_ae (m := F t) hXsum).trans
    (condExp_add (integrable_const c) ((Lp.memLp (W T)).integrable one_le_two) (F t))
  filter_upwards [hs, HeatStoppedMartingale.conditional_stopped I hI ht u] with ω hsum hw
  change μ[(W T : Ω → E) | F t] ω = W t ω at hw
  simp only [Pi.add_apply, condExp_const (F.le t)] at hsum
  exact hsum.trans (congrArg (c + ·) hw)

end HeatHilbertMartingaleRepresentation

#print axioms HeatHilbertMartingaleRepresentation.centered_representation
#print axioms HeatHilbertMartingaleRepresentation.conditional_representation
