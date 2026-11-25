import HeatTorusStateObservability
import HeatPathMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace HeatTorusAdjointAudit

open MeasureTheory Set SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation
open scoped NNReal ENNReal

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate
local notation "Ω" => C(ℝ≥0, ℝ)
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]
local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

/-- The specific Brownian-product adjoint used in the torus observation
counterexample has the path and noise energy asserted in the paper. -/
theorem path_and_noise_energy [Nontrivial (RealState ι)]
    (P : ℝ) (M : RealState ι →L[ℝ] RealState ι)
    {T : ℝ≥0} (t : ℕ → ℝ≥0) (N : ℕ)
    (ht : Monotone t) (ht0 : t 0 = 0) (hN : 1 ≤ N)
    (hstep : ∀ n, n < N → t n < t (n + 1)) (htN : t N = T)
    (g : RealState ι)
    (hprod : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
        MemLp (HeatBrownianProducts.products W t n) 2 μ) :
    let z := HeatTorusObservation.path P M T W t N g
    let v := HeatBackwardNoise.process (family P) (family_continuous P) (family_contraction P)
      M F μ T W t N g hprod
    (∀ ω, Continuous (fun a => z a ω)) ∧ StronglyAdapted F z ∧
      Integrable (fun ω => HeatPathMaximum.value T z ω ^ 2) μ ∧
      Integrable (fun p : ℝ≥0 × Ω => ‖v p‖ ^ 2) (energyMeasure μ T) := by
  dsimp only
  let J := HeatCanonicalNative.scalar T
  have hWa : ∀ a, StronglyMeasurable[F a] (W a) :=
    HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted
  have hzero : family (ι := ι) P 0 = ContinuousLinearMap.id ℝ (RealState ι) := realHeat_zero P
  have hsem (r u : ℝ≥0) : family (ι := ι) P (r + u) = (family P r).comp (family P u) :=
    realHeat_add P r.property u.property
  obtain ⟨_, _, _, _, hzc, hza, ⟨D, hDm, hD0, hDb⟩, _⟩ := HeatBackwardLp.exists_solution F μ T
    (family P) (family_continuous P) (family_contraction P) M (HeatTorusCanonicalIto.basis ι)
    J hzero hsem (HeatCanonicalNative.locality T) W (HeatCanonicalNative.coordinate T) hWa
    (fun ω => ω.continuous) t ht ht0 N hN hstep htN g hprod
  refine ⟨hzc, hza, ?_, ?_⟩
  · exact HeatPathMaximum.integrable_square μ T _
      (fun a => (hza a).measurable.mono (HeatCanonicalUsual56.usualFiltration.le a) le_rfl)
      hzc D hDm hD0 hDb
  · exact (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp _)).norm.integrable_sq

end HeatTorusAdjointAudit

#print axioms HeatTorusAdjointAudit.path_and_noise_energy
