import HeatVariationalForwardModel
import HeatConstructedDuality
import HeatBaseNontrivial

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 3000000
noncomputable section
namespace HeatVariationalDuality
open MeasureTheory Filter SHE.PredictableL2 SHE.HilbertColumns HeatIntervalNormalization HeatConcreteSemigroupInput
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
  (J : SHE.StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "R" => SHE.RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem exists_adjoint (hzero : family 0=ContinuousLinearMap.id ℝ Base)
    (hsem : ∀ s t, family (s+t)=(family s).comp (family t))
    (hsym : ∀ t x y, inner ℝ (family t x) y=inner ℝ x (family t y))
    (hM : ‖M‖≤1) (hMsym : ∀ x y, inner ℝ (M x) y=inner ℝ x (M y))
    (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ) (hlocal : SHE.StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s≤H → J.integral (SHE.StoppedItoInputs.stop F μ H s R)=ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1≤N)
    (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=H) (g₀ g : Base)
    (hP : ∀ n, n≤N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ)
    (U : ℝ≥0 → Ω → HeatIntervalNormalization.Base) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))
    (sol : HeatVariationalForwardModel.Solution F μ H M (HeatTerminalNaturality.integral F μ H basis J) U hU hE g₀) :
    let z := HeatBackwardProcess.state family family_continuous family_contraction M H W t N g
    ∃ Z : ℝ≥0 → Lp HeatIntervalNormalization.Base 2 μ,
      Continuous Z ∧ (∀ a, a≤H → Z a=ᵐ[μ] z a) ∧
      inner ℝ (sol.weak.value H) (Z H)=inner ℝ (sol.weak.value 0) (Z 0)+
        (∫ p,inner ℝ (U p.1 p.2) (z p.1 p.2) ∂energyMeasure μ H) := by
  let z := HeatBackwardProcess.state family family_continuous family_contraction M H W t N g
  let v := HeatBackwardNoise.process family family_continuous family_contraction M F μ H W t N g hP
  let u := sol.weak.input
  let V := sol.weak.value
  have hVc := sol.weak.mean_square_continuous
  have hVa := sol.weak.adapted_values
  have hVu := sol.weak.input_slices
  have hVrep := sol.weak.mild_equation
  obtain ⟨Z,hZc,hZrep,hZa,hzc,hza,⟨D,hDm,hD0,hDb⟩,hz⟩ :=
    HeatBackwardLp.exists_solution F μ H family family_continuous family_contraction M basis J hzero hsem hlocal W hW hWa hWc
      t ht ht0 N hN hstep hTN g hP
  let f := HeatControlAdapted.clamp U H
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm : MemLp f 2 (energyMeasure μ H) := HeatClampedControl.square_integrable F μ H U hU hE
  obtain ⟨C,_,hC⟩ := HeatCompactLpBound.exists_bound μ H V hVc
  have hVad (a : ℝ≥0) (_ha : a≤H) : AEStronglyMeasurable[F a] (V a) μ := by
    obtain ⟨Y,hY,hrep⟩ := hVa a
    exact hY.aestronglyMeasurable.congr hrep.symm
  have hy (a b : ℝ≥0) (hab : a≤b) (_hb : b≤H) : V b=((family (b-a)).compLpL 2 μ) (V a)+
      HeatForwardDrift.value μ H family family_continuous family_contraction f hf hfm a b+
      (I).integral (HeatMildKernelCross.forward F μ H family family_continuous family_contraction M a b u) :=
    HeatForwardLpEquation.equation F μ H family family_continuous family_contraction M basis J hsem f hf hfm g₀ u V hVrep hab
  have hdual := HeatMildDuality.duality F μ H family family_continuous family_contraction M basis J hzero hsem hsym hM hMsym hlocal
    f hf hfm V Z u v hVc hVu C hC z hzc (fun a => (hza a).measurable.mono (F.le a) le_rfl)
    D hDm hD0 hDb hZrep hVad (fun a _ => hZa a) hy hz
  have hctrl : (∫ p,inner ℝ (f p) (z p.1 p.2) ∂energyMeasure μ H)=
      (∫ p,inner ℝ (U p.1 p.2) (z p.1 p.2) ∂energyMeasure μ H) := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    simp only [f,HeatControlAdapted.clamp,min_eq_left hp.2]
  rw [hctrl] at hdual
  exact ⟨Z,hZc,hZrep,hdual⟩

end HeatVariationalDuality
#check @HeatVariationalDuality.exists_adjoint
#print HeatVariationalDuality.exists_adjoint
#print axioms HeatVariationalDuality.exists_adjoint
