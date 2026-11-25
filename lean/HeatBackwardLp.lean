import HeatBackwardGlobalEquation
import HeatBackwardRestriction
import HeatBackwardGlobalEnvelope
import HeatFiniteHorizonLp
import HeatLpIdentity
import HeatActualCellEnergy

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatBackwardLp
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
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

theorem exists_solution (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (hsem : ∀ s t, S (s+t)=(S s).comp (S t)) (hlocal : StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s≤H → J.integral (StoppedItoInputs.stop F μ H s R)=ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1≤N)
    (hstep : ∀ n, n<N → t n<t (n+1)) (hTN : t N=H) (g : E)
    (hP : ∀ n, n≤N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ) :
    let z := HeatBackwardProcess.state S hS hcontr M H W t N g
    let v := HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP
    ∃ Z : ℝ≥0 → Lp E 2 μ, Continuous Z ∧ (∀ a, a≤H → Z a=ᵐ[μ] z a) ∧
      (∀ a, AEStronglyMeasurable[F a] (Z a) μ) ∧
      (∀ ω, Continuous (fun a => z a ω)) ∧ (∀ a, StronglyMeasurable[F a] (z a)) ∧
      (∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0≤D ω) ∧ (∀ a, a≤H → ∀ ω, ‖z a ω‖≤D ω)) ∧
      (∀ a b, a≤b → b≤H → Z a=((S (b-a)).compLpL 2 μ) (Z b)+
        HeatActualCellEnergy.drift F μ H S hS hcontr M a b v-
        (I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v)) := by
  let z := HeatBackwardProcess.state S hS hcontr M H W t N g
  let v := HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP
  have hzc := HeatBackwardProcess.continuous_paths S hS hcontr M hzero W hWc t ht N hN hstep hTN.le g
  have hza : StronglyAdapted F z := HeatBackwardProcess.adapted S hS hcontr M F W hWa t ht0 N hN g (fun n hn => (hP n hn).1)
  obtain ⟨D,hDm,hD0,hDb⟩ := HeatBackwardGlobalEnvelope.exists_envelope S hS hcontr M F μ H J hlocal W hW hWa hWc
    t ht ht0 N hN hTN.le g hP
  have hDbH : ∀ a, a≤H → ∀ ω, ‖z a ω‖≤D ω := by simpa only [hTN] using hDb
  obtain ⟨Z,hZc,hZrep,hZa⟩ := HeatFiniteHorizonLp.exists_version F μ H z hzc hza D hDm hD0 hDbH
  let Dval := fun a b => HeatBackwardDriftKernel.value F μ H S M a b v
  let Ival := fun a b ω => HeatBackwardStochasticKernel.value F μ H S hS hcontr basis J a b v ω
  have hterminal (a : ℝ≥0) (ha : a≤H) : HeatBackwardGluing.Equation μ S Dval Ival z a H := by
    have he := HeatBackwardGlobalEquation.mild_equation S hS hcontr M F μ H basis J hzero hsem hlocal W hW
      t ht ht0 N hN hstep hTN.le g hP a (ha.trans hTN.ge)
    rw [hTN] at he
    filter_upwards [he] with ω hh
    change z a ω=S (H-a) (z H ω)+Dval a H ω-Ival a H ω
    have hterm := HeatBackwardProcess.terminal S hS hcontr M (H := H) hzero W t N hN hstep g ω
    rw [hTN] at hterm
    change z H ω=HeatBrownianProducts.products W t N ω • g at hterm
    rw [hterm]
    exact hh
  refine ⟨Z,hZc,hZrep,hZa,hzc,hza,⟨D,hDm,hD0,hDbH⟩,?_⟩
  intro a b hab hbH
  have hraw := HeatBackwardRestriction.restrict μ S Dval Ival z hsem hab hbH
    (HeatBackwardDriftKernel.split F μ H S hS hcontr M hsem hab hbH v)
    (HeatBackwardStochasticKernel.split_ae F μ H S hS hcontr basis J hsem hab hbH v)
    (hterminal a (hab.trans hbH)) (hterminal b hbH)
  apply HeatLpIdentity.sub μ (S (b-a)) (Z a) (Z b)
    (HeatActualCellEnergy.drift F μ H S hS hcontr M a b v)
    ((I).integral (HeatBackwardKernel.input F μ H S hS hcontr (ContinuousLinearMap.id ℝ E) a b v))
  filter_upwards [hraw,hZrep a (hab.trans hbH),hZrep b hbH,
    HeatActualCellEnergy.drift_ae F μ H S hS hcontr M a b v] with ω hr ha hb hd
  rw [ha,hb,hd]
  exact hr

end HeatBackwardLp
#check @HeatBackwardLp.exists_solution
#print HeatBackwardLp.exists_solution
#print axioms HeatBackwardLp.exists_solution
