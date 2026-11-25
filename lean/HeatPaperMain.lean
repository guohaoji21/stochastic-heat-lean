import HeatCanonicalFixedNoncontrollability
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import HeatCanonicalPhysicalIto
import HeatWeakEnergyPathUniqueness
import HeatForwardNonzero
import HeatControlProgressive
import HeatVariationalForwardModel
import HeatCanonicalSeparable
import HeatCanonicalControlledContinuous

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatPaperMain
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
open HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : IsFiniteMeasure baseMeasure := by unfold baseMeasure;infer_instance
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
abbrev Control := Lp ℝ 2 paperControlMeasure
local instance : MeasurableSpace Control := borel Control
local instance : BorelSpace Control := ⟨rfl⟩
local instance : IsSeparable paperControlMeasure := by unfold paperControlMeasure paperDomainMeasure;infer_instance
local instance : SecondCountableTopology Control := Lp.SecondCountableTopology
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener

theorem noncontrollability (T : ℝ≥0) (hT : 0<T)
    (b : ℝ → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbcompact : HasCompactSupport b)
    (hbsupp : tsupport b⊆Ioo (6:ℝ) 7) (hb0 : ∀ x,0 ≤ b x) (hb1 : ∀ x,b x ≤ 1)
    (hbone : ∀ x∈Ioo (25/4:ℝ) (27/4),b x=1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgcompact : HasCompactSupport g)
    (hgpos : ∀ x,0 ≤ g x) (hgne : g≠0) (hgsupp : tsupport g⊆Ioo (25/4:ℝ) (27/4)) :
    let hbm : AEStronglyMeasurable b baseMeasure := hb.continuous.aestronglyMeasurable
    let hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb0 x)]
      exact hb1 x
    let hgmem : MemLp g 2 baseMeasure := hg.continuous.memLp_of_hasCompactSupport hgcompact
    letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
    ∀ U : ℝ≥0 → C(ℝ≥0,ℝ) → Control,
      (∀ t : ℝ≥0,t ≤ T → Measurable[(inferInstance : MeasurableSpace (Iic t)).prod (F t)]
        (fun p : Iic t × C(ℝ≥0,ℝ) => U p.1 p.2)) →
      Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖U p.1 p.2‖^2) (energyMeasure μ T) →
      let Uf := fun s ω => paperB (U (min s T) ω)
      let I := HeatCanonicalPhysicalIto.integral T
      ∃ hp : IsStronglyProgressive F Uf,
        ∃ hE : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Uf p.1 p.2‖^2) (energyMeasure μ T),
          Nonempty (HeatVariationalForwardModel.Solution F μ T (noise b hbm hbound) I Uf hp hE (hgmem.toLp g)) ∧
          ∀ sol : HeatWeakEnergyModel.Solution F μ T (noise b hbm hbound) I Uf hp hE (hgmem.toLp g),
            0<μ {ω | 0<‖sol.path T ω‖} := by
  dsimp only
  have hbm : AEStronglyMeasurable b baseMeasure := hb.continuous.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb0 x)]
    exact hb1 x
  have hboutside : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → b x=0 := by
    filter_upwards [] with x hx
    exact image_eq_zero_of_notMem_tsupport (fun hm => hx (hbsupp hm))
  exact HeatCanonicalFixedNoncontrollability.exists_nonzero_weak_solution T hT b hbm hbound hboutside
    (Filter.Eventually.of_forall hb0) hbone g hg.continuous hgpos hgne hgsupp
    (hg.continuous.memLp_of_hasCompactSupport hgcompact)

end HeatPaperMain
#check @HeatPaperMain.noncontrollability
#print axioms HeatPaperMain.noncontrollability
