import HeatMildDuality
import HeatControlledMild
import HeatBackwardLp
import HeatClampedControl
import HeatCompactLpBound
import HeatForwardLpEquation

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 3000000
noncomputable section
namespace HeatConstructedDuality
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nontrivial E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ H basis J
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem exists_system (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hsym : ∀ t x y, inner ℝ (S t x) y=inner ℝ x (S t y))
    (hM : ‖M‖≤1) (hMsym : ∀ x y, inner ℝ (M x) y=inner ℝ x (M y))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (hlocal : StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s≤H → J.integral (StoppedItoInputs.stop F μ H s R)=ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1≤N)
    (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=H) (g₀ g : E)
    (hP : ∀ n, n≤N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ)
    (U : ℝ≥0 → Ω → E) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    let z := HeatBackwardProcess.state S hS hcontr M H W t N g
    ∃ A u : Process (E := E) F μ H, ∃ V Z : ℝ≥0 → Lp E 2 μ,
      u=HeatVolterraForcing.orbit F μ H S hS hcontr g₀+A+
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      Continuous V ∧ V 0=Lp.const 2 μ g₀ ∧
      (∀ a, ∃ Y, StronglyMeasurable[F a] Y ∧ V a=ᵐ[μ] Y) ∧
      (∀ᵐ a ∂timeMeasure H, (fun ω => u (a,ω))=ᵐ[μ] V a) ∧
      (∀ a, V a=ᵐ[μ] fun ω => S a g₀+HeatControlConvolution.value H S (HeatControlAdapted.clamp U H) a ω+
        (I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M a u) ω) ∧
      Continuous Z ∧ (∀ a, a≤H → Z a=ᵐ[μ] z a) ∧
      inner ℝ (V H) (Z H)=inner ℝ (V 0) (Z 0)+
        (∫ p,inner ℝ (U p.1 p.2) (z p.1 p.2) ∂energyMeasure μ H) := by
  let z := HeatBackwardProcess.state S hS hcontr M H W t N g
  let v := HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP
  obtain ⟨A,u,V,hu,hVc,hV0,hVa,hVu,hVrep⟩ :=
    HeatControlledMild.exists_solution F μ H S hS hcontr M hsem I hzero hnull U hU hE g₀
  obtain ⟨Z,hZc,hZrep,hZa,hzc,hza,⟨D,hDm,hD0,hDb⟩,hz⟩ :=
    HeatBackwardLp.exists_solution F μ H S hS hcontr M basis J hzero hsem hlocal W hW hWa hWc
      t ht ht0 N hN hstep hTN g hP
  let f := HeatControlAdapted.clamp U H
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfm : MemLp f 2 (energyMeasure μ H) := HeatClampedControl.square_integrable F μ H U hU hE
  obtain ⟨C,_,hC⟩ := HeatCompactLpBound.exists_bound μ H V hVc
  have hVad (a : ℝ≥0) (_ha : a≤H) : AEStronglyMeasurable[F a] (V a) μ := by
    obtain ⟨Y,hY,hrep⟩ := hVa a
    exact hY.aestronglyMeasurable.congr hrep.symm
  have hy (a b : ℝ≥0) (hab : a≤b) (_hb : b≤H) : V b=((S (b-a)).compLpL 2 μ) (V a)+
      HeatForwardDrift.value μ H S hS hcontr f hf hfm a b+
      (I).integral (HeatMildKernelCross.forward F μ H S hS hcontr M a b u) :=
    HeatForwardLpEquation.equation F μ H S hS hcontr M basis J hsem f hf hfm g₀ u V hVrep hab
  have hdual := HeatMildDuality.duality F μ H S hS hcontr M basis J hzero hsem hsym hM hMsym hlocal
    f hf hfm V Z u v hVc hVu C hC z hzc (fun a => (hza a).measurable.mono (F.le a) le_rfl)
    D hDm hD0 hDb hZrep hVad (fun a _ => hZa a) hy hz
  have hctrl : (∫ p,inner ℝ (f p) (z p.1 p.2) ∂energyMeasure μ H)=
      (∫ p,inner ℝ (U p.1 p.2) (z p.1 p.2) ∂energyMeasure μ H) := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    simp only [f,HeatControlAdapted.clamp,min_eq_left hp.2]
  rw [hctrl] at hdual
  exact ⟨A,u,V,Z,hu,hVc,hV0,hVa,hVu,hVrep,hZc,hZrep,hdual⟩

end HeatConstructedDuality
#check @HeatConstructedDuality.exists_system
#print HeatConstructedDuality.exists_system
#print axioms HeatConstructedDuality.exists_system
