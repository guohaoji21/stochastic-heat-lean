import HeatBackwardLocalEquation
import HeatBackwardZero

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatBackwardGlobalEquation
open MeasureTheory Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

include hS hcontr in
theorem mild_equation (hzero : S 0 = ContinuousLinearMap.id ℝ E)
    (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0, s ≤ H → J.integral (StoppedItoInputs.stop F μ H s R) =ᵐ[μ] W s)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0=0) (N : ℕ) (hN : 1 ≤ N)
    (hstep : ∀ n, n < N → t n < t (n+1)) (hT : t N ≤ H) (g : E)
    (hP : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
      MemLp (HeatBrownianProducts.products W t n) 2 μ)
    (a : ℝ≥0) (ha : a≤t N) :
    HeatBackwardProcess.state S hS hcontr M H W t N g a =ᵐ[μ] (fun ω =>
      S (t N-a) (HeatBrownianProducts.products W t N ω • g) +
      HeatBackwardDriftKernel.value F μ H S M a (t N)
        (HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP) ω -
      HeatBackwardStochasticKernel.value F μ H S hS hcontr basis J a (t N)
        (HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP) ω) := by
  let Z := HeatBackwardNoise.process S hS hcontr M F μ H W t N g hP
  let z := HeatBackwardProcess.state S hS hcontr M H W t N g
  let D := fun a b => HeatBackwardDriftKernel.value F μ H S M a b Z
  let I := fun a b ω => HeatBackwardStochasticKernel.value F μ H S hS hcontr basis J a b Z ω
  have hd (a c b : ℝ≥0) (hac : a≤c) (hcb : c≤b) :
      D a b =ᵐ[μ] fun ω => D a c ω+S (c-a) (D c b ω) :=
    HeatBackwardDriftKernel.split F μ H S hS hcontr M hsem hac hcb Z
  have hi (a c b : ℝ≥0) (hac : a≤c) (hcb : c≤b) :
      I a b =ᵐ[μ] fun ω => I a c ω+S (c-a) (I c b ω) :=
    HeatBackwardStochasticKernel.split_ae F μ H S hS hcontr basis J hsem hac hcb Z
  have hself : HeatBackwardGluing.Equation μ S D I z (t N) (t N) := by
    have hn := HeatBackwardZero.noise_self F μ H S hS hcontr basis J (t N) Z
    have hd0 := HeatBackwardZero.drift_self F μ H S M (t N) Z
    filter_upwards [Lp.coeFn_zero E 2 μ] with ω hω
    change z (t N) ω = S (t N-t N) (z (t N) ω)+D (t N) (t N) ω-I (t N) (t N) ω
    change z (t N) ω = _+HeatBackwardDriftKernel.value F μ H S M (t N) (t N) Z ω-
      HeatBackwardStochasticKernel.value F μ H S hS hcontr basis J (t N) (t N) Z ω
    rw [hn,hd0]
    simp only [tsub_self,hzero,ContinuousLinearMap.id_apply,Pi.zero_apply,hω,add_zero,sub_zero]
  have hcell (j : ℕ) (hj : 1≤j) (hjN : j≤N) :
      HeatBackwardGluing.Equation μ S D I z (t (j-1)) (t j) :=
    HeatBackwardLocalEquation.local_equation S hS hcontr M F μ H basis J hzero hsem hlocal W hW
      t ht N hN hstep hT g hP ⟨j,Finset.mem_Icc.mpr ⟨hj,hjN⟩⟩ (t (j-1))
      ⟨le_rfl,ht (Nat.sub_le _ _)⟩
  have hgrid := HeatBackwardGluing.on_grid μ S D I z hsem t ht N hd hi hself hcell
  have ha0 : t 0≤a := by rw [ht0];exact zero_le
  obtain ⟨j,hj,hjN,hlo,hhi⟩ := HeatBackwardGluing.exists_cell t ht N hN a ha0 ha
  have he := HeatBackwardLocalEquation.local_equation S hS hcontr M F μ H basis J hzero hsem hlocal W hW
    t ht N hN hstep hT g hP ⟨j,Finset.mem_Icc.mpr ⟨hj,hjN⟩⟩ a ⟨hlo,hhi⟩
  have hg := HeatBackwardGluing.trans μ S D I z hsem hhi (ht hjN)
    (hd a (t j) (t N) hhi (ht hjN)) (hi a (t j) (t N) hhi (ht hjN)) he (hgrid j hjN)
  filter_upwards [hg] with ω hω
  have hterm := HeatBackwardProcess.terminal S hS hcontr M (H := H) hzero W t N hN hstep g ω
  exact hω.trans (congrArg (fun x => S (t N-a) x+D a (t N) ω-I a (t N) ω) hterm)

end HeatBackwardGlobalEquation
#check @HeatBackwardGlobalEquation.mild_equation
#print axioms HeatBackwardGlobalEquation.mild_equation
