import HeatLogObservation
import HeatUniformMass
import HeatVariationalSystem
import HeatBackwardEndpointPairing
import HeatControlAdjointPairing
import HeatIntegralCauchy

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace HeatForwardNonzero
open MeasureTheory Filter Set SHE.PredictableL2 SHE.HilbertColumns
open HeatIntervalNormalization HeatConcreteSemigroupInput HeatCanonicalPredictableSolution HeatRestrictionAdjoint
open scoped NNReal ENNReal BigOperators
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : Nontrivial Base := HeatBaseNontrivial.nontrivial
abbrev Control := Lp ℝ 2 paperControlMeasure
local instance : MeasurableSpace Control := borel Control
local instance : BorelSpace Control := ⟨rfl⟩
local instance : IsSeparable paperControlMeasure := by unfold paperControlMeasure paperDomainMeasure;infer_instance
local instance : SecondCountableTopology Control := Lp.SecondCountableTopology
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable (basis : HilbertBasis κ ℝ Base)
  (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "R" => SHE.RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem not_ae_zero (hH : 0<H) (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (hlocal : SHE.StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0,s ≤ H → (J.integral (SHE.StoppedItoInputs.stop F μ H s R) : Ω → ℝ)=ᵐ[μ] W s)
    (hWa : ∀ s,StronglyMeasurable[F s] (W s)) (hWc : ∀ ω,Continuous (fun s => W s ω))
    (b : ℝ → ℝ) (hb : AEStronglyMeasurable b baseMeasure)
    (hbound : ∀ᵐ x ∂baseMeasure,‖b x‖ ≤ 1)
    (hsupp : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → b x=0)
    (hbpos : ∀ᵐ x ∂baseMeasure,0 ≤ b x) (hbone : ∀ x∈Ioo (25/4:ℝ) (27/4),b x=1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgpos : ∀ x,0 ≤ g x) (hgne : g≠0)
    (hgsupp : tsupport g⊆Ioo (25/4:ℝ) (27/4)) (hgmem : MemLp g 2 baseMeasure)
    (U : ℝ≥0 × Ω → Control) (hU : MemLp U 2 (energyMeasure μ H))
    (Uf : ℝ≥0 → Ω → Base) (hUf : IsStronglyProgressive F Uf)
    (hEf : Integrable (fun p : ℝ≥0 × Ω => ‖Uf p.1 p.2‖^2) (energyMeasure μ H))
    (hforce : Function.uncurry Uf=ᵐ[energyMeasure μ H] fun p => paperB (U p))
    (sol : HeatVariationalForwardModel.Solution F μ H (noise b hb hbound) I Uf hUf hEf (hgmem.toLp g)) :
    ¬sol.weak.path H=ᵐ[μ] (fun _ => (0:Base)) := by
  intro hzero
  let G := hgmem.toLp g
  obtain ⟨c,hc,hmass⟩ := HeatUniformMass.exists_lower_bound g hg hgpos hgne hgsupp hgmem
    b hb hbound hbpos hbone (H:ℝ)
  have hGsupport : ∀ᵐ x ∂baseMeasure,x∉Ioo (6:ℝ) 7 → G x=0 := by
    filter_upwards [hgmem.coeFn_toLp] with x hx hnot
    rw [hx]
    apply image_eq_zero_of_notMem_tsupport
    intro hxg
    have hh := hgsupp hxg
    exact hnot ⟨by norm_num at hh ⊢;linarith [hh.1],by norm_num at hh ⊢;linarith [hh.2]⟩
  have hv : sol.weak.value H=0 := by
    apply Lp.ext
    filter_upwards [sol.weak.path_version H le_rfl,hzero,Lp.coeFn_zero Base 2 μ] with ω hp hz hzz
    rw [←hp,hz,hzz]
    rfl
  have hM : ‖noise b hb hbound‖ ≤ 1 :=
    SHEStochastic.BoundedFieldOperator.operator_norm (HeatScalarMultiplier.field baseMeasure b hb hbound)
  have hMsym : ∀ x y : Base,inner ℝ (noise b hb hbound x) y=inner ℝ x (noise b hb hbound y) :=
    (HeatMultiplierAdjoint.scalar_multiplier_self_adjoint baseMeasure b hb hbound).isSymmetric
  have hineq (L : ℝ) (hL : 1 ≤ L) :
      c^2 ≤ (∫ p,‖U p‖^2 ∂energyMeasure μ H)*(2*‖G‖^2*Real.exp (-4*L)) := by
    obtain ⟨N,hN,hbefore,hend⟩ := HeatLogPartition.exists_partition L hL H hH
    let d := HeatLogPartition.lengths L hL
    let t := HeatClippedPartition.nodes d H
    have ht : Monotone t := HeatClippedPartition.nodes_mono d H
    have hprops := HeatClippedPartition.nodes_properties d H (HeatLogPartition.positive L hL) hN hbefore hend
    have hT : ∀ n,n ≤ N → t n ≤ H := fun n _ => hprops.2.2.2 n
    have hP := HeatBrownianProducts.products_properties F μ H J hlocal W hW hWa t ht N hT
    obtain ⟨back,hdual⟩ := HeatVariationalSystem.exists_adjoint F μ H (noise b hb hbound) basis J hM hMsym
      hnull hlocal W hW hWa hWc t ht hprops.1 N hN hprops.2.2.1 hprops.2.1 G G hP Uf hUf hEf sol
    have hinit := HeatBackwardEndpointPairing.initial μ H family family_continuous family_contraction
      (noise b hb hbound) W t ht hprops.1 N hN hprops.2.2.1 hprops.2.1 G G
      sol.weak.value back.value sol.weak.initial_value (back.value_path 0 zero_le)
    rw [hv,inner_zero_left,hinit] at hdual
    let z := HeatBackwardModel.path H (noise b hb hbound) W t N G
    let obs := fun p : ℝ≥0 × Ω => paperBstar (z p.1 p.2)
    have hpair : (∫ p,inner ℝ (Uf p.1 p.2) (z p.1 p.2) ∂energyMeasure μ H)=
        ∫ p,inner ℝ (U p) (obs p) ∂energyMeasure μ H := by
      apply integral_congr_ae
      filter_upwards [hforce] with p hp
      change Uf p.1 p.2=paperB (U p) at hp
      rw [hp]
      exact HeatControlAdjointPairing.pairing _ _
    rw [hpair] at hdual
    change 0=inner ℝ (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound)
      (fun k => t k-t (k-1)) N G 0) G+(∫ p,inner ℝ (U p) (obs p) ∂energyMeasure μ H) at hdual
    have hsNN := HeatClippedPartition.reverse_sum t ht N
    have ht0 : t 0=0 := hprops.1
    have htN : t N=H := hprops.2.1
    rw [ht0,htN,tsub_zero] at hsNN
    have hsreal : (∑ k∈Finset.range N,((t (N-k)-t (N-k-1):ℝ≥0):ℝ))=(H:ℝ) := by
      exact_mod_cast hsNN
    have hmass' := hmass (fun k => t k-t (k-1)) N hsreal
    have hmass'' : c ≤ inner ℝ (HeatBackwardChain.stateAt (HeatPaperCovariance.K b hb hbound)
        (fun k => t k-t (k-1)) N G 0) G := by
      exact hmass'.trans_eq (real_inner_comm _ _)
    have hobs := HeatLogObservation.bound F μ H J hlocal W hW hWa b hb hbound hsupp L hL N hN hbefore hend
      G hGsupport I back
    have hobsM : StronglyMeasurable obs := paperBstar.continuous.comp_stronglyMeasurable
      (back.path_predictable.mono (predictable_le_product F))
    have hobsE : Integrable (fun p => ‖obs p‖^2) (energyMeasure μ H) :=
      HeatPathObservation.integrable μ H z back.path_continuous
        (back.path_predictable.mono (predictable_le_product F)) back.maximum_energy paperBstar
    have hobs2 : MemLp obs 2 (energyMeasure μ H) :=
      (memLp_two_iff_integrable_sq_norm hobsM.aestronglyMeasurable).mpr hobsE
    have hcs := HeatIntegralCauchy.inner_square (energyMeasure μ H) U obs hU hobs2
    have hnorm : c^2 ≤ (∫ p,inner ℝ (U p) (obs p) ∂energyMeasure μ H)^2 := by
      have hle : c ≤ -(∫ p,inner ℝ (U p) (obs p) ∂energyMeasure μ H) := by linarith
      nlinarith
    exact hnorm.trans (hcs.trans (mul_le_mul_of_nonneg_left hobs
      (integral_nonneg fun p => sq_nonneg _)))
  have hlim : Tendsto (fun n : ℕ => (∫ p,‖U p‖^2 ∂energyMeasure μ H)*
      (2*‖G‖^2*Real.exp (-4*((n:ℝ)+1)))) atTop (nhds 0) := by
    have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hn' : Tendsto (fun n : ℕ => -4*((n:ℝ)+1)) atTop atBot := hn.const_mul_atTop_of_neg (by norm_num)
    simpa using ((Real.tendsto_exp_atBot.comp hn').const_mul (2*‖G‖^2)).const_mul (∫ p,‖U p‖^2 ∂energyMeasure μ H)
  have hle : c^2 ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n => hineq ((n:ℝ)+1) (by
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith))
  nlinarith

end HeatForwardNonzero
#check @HeatForwardNonzero.not_ae_zero
#print axioms HeatForwardNonzero.not_ae_zero
