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
namespace HeatCanonicalFixedNoncontrollability
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatIntervalNormalization HeatConcreteSemigroupInput
open HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
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

theorem exists_nonzero_weak_solution (T : ℝ≥0) (hT : 0<T) (b : ℝ → ℝ)
    (hb : AEStronglyMeasurable b baseMeasure) (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1)
    (hbsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → b x=0)
    (hbpos : ∀ᵐ x ∂baseMeasure,0 ≤ b x) (hbone : ∀ x∈Ioo (25/4:ℝ) (27/4),b x=1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgpos : ∀ x,0 ≤ g x) (hgne : g≠0)
    (hgsupp : tsupport g⊆Ioo (25/4:ℝ) (27/4)) (hgmem : MemLp g 2 baseMeasure) :
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
          Nonempty (HeatVariationalForwardModel.Solution F μ T (noise b hb hbound) I Uf hp hE (hgmem.toLp g)) ∧
          ∀ sol : HeatWeakEnergyModel.Solution F μ T (noise b hb hbound) I Uf hp hE (hgmem.toLp g),
            0<μ {ω | 0<‖sol.path T ω‖} := by
  letI : MeasurableSpace C(ℝ≥0,ℝ) := HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
  letI : IsSeparable μ := HeatCanonicalSeparable.completed_separable
  letI : MeasurableSpace (SHE.HilbertColumns.Space Unit ℝ) := borel _
  letI : BorelSpace (SHE.HilbertColumns.Space Unit ℝ) := ⟨rfl⟩
  intro U hUraw hE
  have hU := (HeatControlProgressive.original_iff_strong F T U).mp hUraw
  let basis := HeatCanonicalPhysicalIto.basis
  let J := HeatCanonicalNative.scalar T
  let I := HeatTerminalNaturality.integral F μ T basis J
  let Ue := fun s ω => U (min s T) ω
  have hUe : IsStronglyProgressive F Ue := HeatFiniteControlExtension.extend F T U hU
  have heq := HeatFiniteControlExtension.energy_ae μ T U
  have hEe : Integrable (fun p : ℝ≥0 × C(ℝ≥0,ℝ) => ‖Ue p.1 p.2‖^2) (energyMeasure μ T) :=
    hE.congr (heq.fun_comp (fun y : Control => ‖y‖^2)).symm
  have hp : IsStronglyProgressive F (fun s ω => paperB (Ue s ω)) :=
    HeatControlInjection.progressive (E := Base) F paperB Ue hUe
  have henergy := HeatControlInjection.energy (E := Base) F μ T paperB Ue hUe hEe
  refine ⟨hp,henergy,?_,?_⟩
  · exact HeatVariationalForwardModel.exists_solution F μ T (noise b hb hbound) basis J hT
      (HeatCanonicalNative.locality T) (HeatCanonicalNative.continuous_stopped T)
      HeatCanonicalNullComplete.contains_nulls (SHEStochastic.NativeScalarBDG.constant 3)
      (HeatCanonicalBDG.hilbert_bdg basis T 3) (fun s ω => paperB (Ue s ω)) hp henergy (hgmem.toLp g)

  · intro sol
    obtain ⟨full⟩ := HeatVariationalForwardModel.exists_solution F μ T (noise b hb hbound) basis J hT
      (HeatCanonicalNative.locality T) (HeatCanonicalNative.continuous_stopped T)
      HeatCanonicalNullComplete.contains_nulls (SHEStochastic.NativeScalarBDG.constant 3)
      (HeatCanonicalBDG.hilbert_bdg basis T 3) (fun s ω => paperB (Ue s ω)) hp henergy (hgmem.toLp g)
    have hUeM : StronglyMeasurable (Function.uncurry Ue) := by
      have he : HeatControlAdapted.clamp Ue T=Function.uncurry Ue := by
        funext p
        change U (min (min p.1 T) T) p.2=U (min p.1 T) p.2
        rw [min_assoc,min_self]
      have hm := HeatControlAdapted.clamp_measurable F Ue hUe T
      rw [he] at hm
      exact hm
    have hU2 : MemLp (Function.uncurry Ue) 2 (energyMeasure μ T) :=
      (memLp_two_iff_integrable_sq_norm hUeM.aestronglyMeasurable).mpr hEe
    have hne := HeatForwardNonzero.not_ae_zero F μ T basis J hT HeatCanonicalNullComplete.contains_nulls
      (HeatCanonicalNative.locality T) HeatCanonicalWiener56.coordinate (HeatCanonicalNative.coordinate T)
      HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted (fun ω => ω.continuous)
      b hb hbound hbsupp hbpos hbone g hg hgpos hgne hgsupp hgmem
      (Function.uncurry Ue) hU2 (fun s ω => paperB (Ue s ω)) hp henergy
      (Filter.EventuallyEq.rfl) full
    have hpaths := HeatWeakEnergyPathUniqueness.path_same F μ T (noise b hb hbound) basis J
      (fun s ω => paperB (Ue s ω)) hp henergy (hgmem.toLp g)
      sol (HeatWeakEnergyModel.of_weak F μ T (noise b hb hbound) I (fun s ω => paperB (Ue s ω)) hp henergy (hgmem.toLp g) full.weak)
      (HeatCanonicalNative.locality T)
    apply bot_lt_iff_ne_bot.mpr
    intro hzero
    apply hne
    have hz := (measure_eq_zero_iff_ae_notMem).mp hzero
    filter_upwards [hz,hpaths] with ω hω hpath
    have hn : ¬0<‖sol.path T ω‖ := hω
    have h0 : sol.path T ω=0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg _))
    have he := hpath T le_rfl
    change sol.path T ω=full.weak.path T ω at he
    exact he.symm.trans h0

end HeatCanonicalFixedNoncontrollability
#check @HeatCanonicalFixedNoncontrollability.exists_nonzero_weak_solution
#print axioms HeatCanonicalFixedNoncontrollability.exists_nonzero_weak_solution
