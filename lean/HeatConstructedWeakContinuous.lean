import HeatWeakControlled
import HeatControlledMild
import HeatProgressiveControl
import HeatGeneralContinuous
import HeatForcingIdentification
import HeatPaperSmoothing
import HeatClampedControl
import HeatBaseNontrivial
import HeatCanonicalPredictableSolution

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatConstructedWeakContinuous
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization
open HeatWeakDirichlet HeatConcreteSemigroupInput HeatCanonicalPredictableSolution
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : IsSeparable baseMeasure := by unfold baseMeasure;infer_instance
local instance : SecondCountableTopology Base := Lp.SecondCountableTopology
local instance : Nontrivial Base := HeatBaseNontrivial.nontrivial
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (M : Base →L[ℝ] Base) (basis : HilbertBasis κ ℝ Base)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem exists_solution (hH : 0<H) (hlocal : StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 (I) B)
    (U : ℝ≥0 → Ω → Base) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : Base) :
    let f := HeatControlAdapted.clamp U H
    let hf := (HeatControlAdapted.clamp_measurable F U hU H).measurable
    let hfm := HeatClampedControl.square_integrable F μ H U hU hE
    ∃ A u : Process (E := Base) F μ H, ∃ V : ℝ≥0 → Lp Base 2 μ,
      u=HeatVolterraForcing.orbit F μ H family family_continuous family_contraction g+A+
        HeatVolterraFixedPoint.convolution F μ H family family_continuous family_contraction M family_semigroup (I) u ∧
      Continuous V ∧ V 0=Lp.const 2 μ g ∧
      (∀ t, ∃ Z : Ω → Base, StronglyMeasurable[F t] Z ∧ V t=ᵐ[μ] Z) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t) ∧
      (∀ t, V t=ᵐ[μ] fun ω => family t g+HeatControlConvolution.value H family f t ω+
        (I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u) ω) ∧
      ∃ Y : ℝ≥0 → Ω → Base, (∀ ω, Continuous (fun t => Y t ω)) ∧ StronglyAdapted F Y ∧
        StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧ (Y 0=ᵐ[μ] fun _ => g) ∧
        u=ᵐ[energyMeasure μ H] Function.uncurry Y ∧
        Integrable (fun p : ℝ≥0 × Ω => ‖Y p.1 p.2‖^2) (energyMeasure μ H) ∧
        (∀ t, t≤H → Y t=ᵐ[μ] V t) ∧
        (∀ T : ℝ≥0, T≤H → ∀ φ ψ : Base, weakLaplacian φ ψ →
          ((innerSL ℝ φ).compLpL 2 μ) (V T)=Lp.const 2 μ (inner ℝ φ g)+
            ((innerSL ℝ φ).compLpL 2 μ) (HeatAmbientDrift.value μ H f hf hfm T)+
            (∫ t,((innerSL ℝ ψ).compLpL 2 μ) (V t) ∂timeMeasure T)+
            ((innerSL ℝ φ).compLpL 2 μ) ((I).integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M u)))) := by
  let f := HeatControlAdapted.clamp U H
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm : MemLp f 2 (energyMeasure μ H) := HeatClampedControl.square_integrable F μ H U hU hE
  obtain ⟨A,u,V,hu,hVc,hV0,hVa,hVs,hVr⟩ := HeatControlledMild.exists_solution F μ H family
    family_continuous family_contraction M family_semigroup (I) paperHeat_zero hnull U hU hE g
  obtain ⟨_,X,hXc,hXa,hXp,_,hXr,D,hDm,hD0,hDb,_⟩ :=
    HeatProgressiveControl.exists_version F μ H family family_continuous family_contraction hnull U hU hE
  let hm : ∀ t, StronglyMeasurable (X t) := fun t => (hXa t).mono (F.le t)
  let Q := HeatVersionLp.value μ X hm D hDm hDb
  have hQc : Continuous Q := HeatVersionLp.continuous μ X hm D hDm hD0 hDb hXc
  have hQr (t : ℝ≥0) : Q t=ᵐ[μ] HeatControlConvolution.value H family f t :=
    (HeatVersionLp.value_ae μ X hm D hDm hDb t).trans (hXr t)
  let V₀ := HeatMildSolution.value F μ H family family_continuous family_contraction M (I) g u
  have hVeq (t : ℝ≥0) : V t=V₀ t+Q t := by
    apply Lp.ext
    filter_upwards [hVr t,Lp.coeFn_add (V₀ t) (Q t),
      Lp.coeFn_add (Lp.const 2 μ (family t g)) ((I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u)),
      Lp.coeFn_const 2 μ (family t g),hQr t] with ω hv hs hn hg hq
    rw [hv,hs]
    change family t g+HeatControlConvolution.value H family f t ω+_=
      (Lp.const 2 μ (family t g)+(I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u)) ω+Q t ω
    rw [hn]
    simp only [Pi.add_apply,hg,Function.const_apply,hq]
    abel
  have hweak (T : ℝ≥0) (hT : T≤H) (φ ψ : Base) (hφ : weakLaplacian φ ψ) :
      ((innerSL ℝ φ).compLpL 2 μ) (V T)=Lp.const 2 μ (inner ℝ φ g)+
        ((innerSL ℝ φ).compLpL 2 μ) (HeatAmbientDrift.value μ H f hf hfm T)+
        (∫ t,((innerSL ℝ ψ).compLpL 2 μ) (V t) ∂timeMeasure T)+
        ((innerSL ℝ φ).compLpL 2 μ) ((I).integral (StoppedItoInputs.stop F μ H T (HeatWeakStochasticInput.noise F μ H M u))) := by
    have hj := HeatControlJoint.integrable_of_version μ H family family_continuous family_contraction f hf
      X (hXp.mono (predictable_le_product F)) D hDm hDb hXr T
    have heq : V=(fun t => V₀ t+Q t) := funext hVeq
    rw [heq]
    exact HeatWeakControlled.weak_equation F μ H M basis J g u f hf hfm Q hQc hQr hT hj φ ψ hφ
  let G : ℝ≥0 → Ω → Base := fun t ω => family t g+X t ω
  have hGc (ω : Ω) : Continuous (fun t => G t ω) := (family_continuous g).add (hXc ω)
  have hGa : StronglyAdapted F G := fun t => stronglyMeasurable_const.add (hXa t)
  have hGp := SHE.ContinuousPredictable.stronglyMeasurable F G hGa hGc
  have hVG (t : ℝ≥0) : V t=ᵐ[μ] fun ω => G t ω+(I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u) ω := by
    filter_upwards [hVr t,hXr t] with ω hv hx
    exact hv.trans (congrArg (fun z => family t g+z+(I).integral (HeatVolterraSlice.slice F μ H family family_continuous family_contraction M t u) ω) hx.symm)
  have hAG := HeatForcingIdentification.forcing_ae F μ H family family_continuous family_contraction M family_semigroup (I)
    (HeatVolterraForcing.orbit F μ H family family_continuous family_contraction g+A) u hu V hVs G
      (hGp.mono (predictable_le_product F)).measurable hVG
  have hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : Base,
      ‖family δ (family τ x)-family τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖ := by
    intro τ δ hτ x
    exact HeatPaperSmoothing.paper_bound (by exact_mod_cast hτ) δ.property (by norm_num) (by norm_num) x
  obtain ⟨Y,hYc,hYa,hYp,hueq,hYr⟩ := HeatGeneralContinuous.exists_version F μ H family family_continuous
    family_contraction M family_semigroup hsmooth basis J hH hlocal hversions hnull B hB
      (HeatVolterraForcing.orbit F μ H family family_continuous family_contraction g+A) u hu G hGc hGa hAG
      (fun ω => ‖g‖+D ω) ((memLp_const ‖g‖).add hDm) (fun ω => add_nonneg (norm_nonneg _) (hD0 ω))
      (fun t ω => (norm_add_le _ _).trans (add_le_add (family_contraction _ _) (hDb t ω)))
  have hYV (t : ℝ≥0) (ht : t≤H) : Y t=ᵐ[μ] V t := (hYr t ht).trans (hVG t).symm
  have hY0 : Y 0=ᵐ[μ] fun _ => g := by
    have hh := hYV 0 zero_le
    rw [hV0] at hh
    exact hh.trans (Lp.coeFn_const 2 μ g)
  have henergy := ((memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq).congr
    (hueq.fun_comp (fun z : Base => ‖z‖^2))
  exact ⟨A,u,V,hu,hVc,hV0,hVa,hVs,hVr,Y,hYc,hYa,hYp,hY0,hueq,henergy,hYV,hweak⟩

end HeatConstructedWeakContinuous
#check @HeatConstructedWeakContinuous.exists_solution
#print HeatConstructedWeakContinuous.exists_solution
#print axioms HeatConstructedWeakContinuous.exists_solution
