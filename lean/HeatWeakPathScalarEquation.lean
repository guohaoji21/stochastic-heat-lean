import HeatWeakForwardModel
import HeatScalarDampingNNReal
import SHE.LpIntegralFubini

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatWeakPathScalarEquation
open MeasureTheory Filter SHE SHE.PredictableL2 HeatIntervalNormalization HeatWeakDirichlet
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (M : Base →L[ℝ] Base) (I : StandardTerminalIto (C := Base) (E := Base) F μ H)
  (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
  (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base)
  (sol : HeatWeakForwardModel.Solution F μ H M I U hU hE g)

theorem integrated_path {T : ℝ≥0} (hT : T≤H) (ψ : Base) :
    (∫ t,((innerSL ℝ ψ).compLpL 2 μ) (sol.value t) ∂timeMeasure T)=ᵐ[μ]
      fun ω => ∫ t,inner ℝ ψ (sol.path t ω) ∂timeMeasure T := by
  have hpm := sol.path_predictable.mono (predictable_le_product F)
  have hm : MemLp (Function.uncurry sol.path) 2 (energyMeasure μ H) :=
    (memLp_two_iff_integrable_sq_norm hpm.aestronglyMeasurable).mpr sol.path_energy
  have hmT := hm.mono_measure (Measure.prod_mono (HeatTimeRestriction.mono hT) le_rfl)
  have hInt := (innerSL ℝ ψ).integrable_comp (hmT.integrable (by norm_num))
  have hc : Continuous (fun t => ((innerSL ℝ ψ).compLpL 2 μ) (sol.value t)) :=
    ((innerSL ℝ ψ).compLpL 2 μ).continuous.comp sol.mean_square_continuous
  have hr : ∀ᵐ t ∂timeMeasure T,
      ((innerSL ℝ ψ).compLpL 2 μ) (sol.value t)=ᵐ[μ] fun ω => inner ℝ ψ (sol.path t ω) := by
    filter_upwards [timeMeasure_ae_mem T] with t ht
    filter_upwards [(innerSL ℝ ψ).coeFn_compLpL (sol.value t),sol.path_version t (ht.2.trans hT)] with ω he hp
    rw [he,←hp]
    rfl
  exact SHE.LpIntegralFubini.integral_ae μ (timeMeasure T) _
    (HeatCompactTimeIntegrability.of_continuous _ hc T) _ hInt hr

theorem equation {T : ℝ≥0} (hT : T≤H) (φ ψ : Base) (hg : weakLaplacian φ ψ) :
    ∀ᵐ ω ∂μ, inner ℝ φ (sol.path T ω)=inner ℝ φ g+
      (∫ s,inner ℝ φ (HeatControlAdapted.clamp U H (s,ω)) ∂timeMeasure T)+
      (∫ s,inner ℝ ψ (sol.path s ω) ∂timeMeasure T)+
      inner ℝ φ (I.integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.input)) ω) := by
  let f := HeatControlAdapted.clamp U H
  have hf := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm := HeatClampedControl.square_integrable F μ H U hU hE
  let R := HeatAmbientDrift.value μ H f hf hfm T
  let N := I.integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M sol.input))
  let A : Lp ℝ 2 μ := Lp.const 2 μ (inner ℝ φ g)
  let B := ((innerSL ℝ φ).compLpL 2 μ) R
  let C := ∫ t,((innerSL ℝ ψ).compLpL 2 μ) (sol.value t) ∂timeMeasure T
  let D := ((innerSL ℝ φ).compLpL 2 μ) N
  have hw : ((innerSL ℝ φ).compLpL 2 μ) (sol.value T)=A+B+C+D := sol.weak_equation T hT φ ψ hg
  have hlhs := (innerSL ℝ φ).coeFn_compLpL (sol.value T)
  rw [hw] at hlhs
  filter_upwards [sol.path_version T hT,hlhs,Lp.coeFn_add (A+B+C) D,Lp.coeFn_add (A+B) C,
    Lp.coeFn_add A B,Lp.coeFn_const 2 μ (inner ℝ φ g),
    (innerSL ℝ φ).coeFn_compLpL R,HeatAmbientDrift.value_ae μ H f hf hfm hT,
    integrated_path F μ H M I U hU hE g sol hT ψ,
    (innerSL ℝ φ).coeFn_compLpL N,
    HeatControlConvolution.time_memLp μ H f hf hfm] with ω hpath hl hsum1 hsum2 hsum3 hA hB hR hC hD hfω
  change (A+B+C+D) ω=inner ℝ φ (sol.value T ω) at hl
  change (A+B+C+D) ω=(A+B+C) ω+D ω at hsum1
  change (A+B+C) ω=(A+B) ω+C ω at hsum2
  change (A+B) ω=A ω+B ω at hsum3
  change A ω=inner ℝ φ g at hA
  change B ω=inner ℝ φ (R ω) at hB
  change C ω=(∫ s,inner ℝ ψ (sol.path s ω) ∂timeMeasure T) at hC
  change D ω=inner ℝ φ (N ω) at hD
  rw [hsum1,hsum2,hsum3,hA,hB,hR,hC,hD,←hpath] at hl
  have hft := (hfω.mono_measure (HeatTimeRestriction.mono hT)).integrable (by norm_num)
  have hc := (innerSL ℝ φ).integral_comp_comm hft
  change (∫ s,inner ℝ φ (f (s,ω)) ∂timeMeasure T)=inner ℝ φ (∫ s,f (s,ω) ∂timeMeasure T) at hc
  rw [←hc] at hl
  exact hl.symm

end HeatWeakPathScalarEquation
#check @HeatWeakPathScalarEquation.integrated_path
#print axioms HeatWeakPathScalarEquation.integrated_path
#check @HeatWeakPathScalarEquation.equation
#print HeatWeakPathScalarEquation.equation
#print axioms HeatWeakPathScalarEquation.equation
