import HeatMildSolution
import HeatTerminalNaturality
import HeatHilbertFutureCenter

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
namespace HeatMildRestart
open MeasureTheory Filter Set SHE SHE.PredictableL2 HeatVolterraSlice HeatPredictableStateInput HeatMildSolution
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)

include hsem in
theorem past_kernel {a b : ℝ≥0} (hab : a ≤ b) (u : Process (E := E) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    ((S (b-a)).compLpL 2 ν) (slice F μ H S hS hcontr M a u) =
      StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply SHE.PastItoAlgebra.eq_of_ambient_ae
  have hmap := ae_eq_of_ae_eq_trim ((S (b-a)).coeFn_compLpL (slice F μ H S hS hcontr M a u))
  filter_upwards [hmap,slice_ae F μ H S hS hcontr M a u,
    StoppedItoInputs.stop_ae F μ H a (factor F μ H S hS hcontr M b u),
    factor_ae F μ H S hS hcontr M b u] with p hm hs ht hf
  rw [hm,hs,ht]
  by_cases hp : p.1 < a
  · rw [Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (a:ℝ) from hp),hf]
    simp only [HeatVolterraKernel.raw, if_pos hp]
    have htime : b-a+(a-p.1) = b-p.1 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_add, NNReal.coe_sub hab,NNReal.coe_sub hp.le,NNReal.coe_sub (hp.le.trans hab)]
      ring
    have hh := congrArg (fun L : E →L[ℝ] E => L (M (u p))) (hsem (b-a) (a-p.1))
    rw [htime] at hh
    exact hh.symm
  · rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (a:ℝ) from hp)]
    simp only [HeatVolterraKernel.raw, if_neg hp, map_zero]

theorem map_constant (A : E →L[ℝ] E) (g : E) :
    (A.compLpL 2 μ) (Lp.const 2 μ g) = Lp.const 2 μ (A g) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (Lp.const 2 μ g),Lp.coeFn_const 2 μ g,
    Lp.coeFn_const 2 μ (A g)] with ω ha hg hAg
  rw [ha,hg,hAg]
  rfl

variable {κ : Type*} [Countable κ] (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := SHE.HilbertColumns.Space Unit ℝ) (E := ℝ) F μ H)
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

include hsem in
theorem restart {a b : ℝ≥0} (hab : a ≤ b) (g : E) (u : Process (E := E) F μ H) :
    value F μ H S hS hcontr M I g u b =
      ((S (b-a)).compLpL 2 μ) (value F μ H S hS hcontr M I g u a) +
      ((I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)) -
        (I).integral (StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u))) := by
  unfold value
  rw [map_add,map_constant μ,HeatTerminalNaturality.commutes,
    past_kernel F μ H S hS hcontr M hsem hab]
  have hdet : S (b-a) (S a g) = S b g := by
    have hh := congrArg (fun L : E →L[ℝ] E => L g) (hsem (b-a) a)
    rw [tsub_add_cancel_of_le hab] at hh
    exact hh.symm
  rw [hdet]
  change _ + (I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)) = _
  abel

include hsem in
theorem conditional_mean (hlocal : StandardTerminalPastLocality J) {a b : ℝ≥0}
    (hab : a ≤ b) (g : E) (u : Process (E := E) F μ H) :
    μ[(value F μ H S hS hcontr M I g u b : Ω → E) | F a] =ᵐ[μ]
      (fun ω => S (b-a) (value F μ H S hS hcontr M I g u a ω)) := by
  let A := S (b-a)
  let V := value F μ H S hS hcontr M I g u a
  have hV : MemLp (fun ω => A (V ω)) 2 μ := A.comp_memLp' (Lp.memLp V)
  obtain ⟨Z,hZ,hrep⟩ := value_adapted F μ H S hS hcontr M I g u a
  have hVm : AEStronglyMeasurable[F a] (fun ω => A (V ω)) μ :=
    (A.continuous.comp_stronglyMeasurable hZ).aestronglyMeasurable.congr (hrep.fun_comp A).symm
  apply HeatHilbertFutureCenter.conditional_mean_of_mild_decomposition I (HeatTerminalNaturality.locality F μ H basis J hlocal) hab
    (factor F μ H S hS hcontr M b u) (fun ω => A (V ω)) _ (hV.integrable one_le_two) hVm
  rw [restart F μ H S hS hcontr M hsem basis J hab]
  filter_upwards [Lp.coeFn_add ((A.compLpL 2 μ) V)
    ((I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)) -
      (I).integral (StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u))),
    A.coeFn_compLpL V,
    Lp.coeFn_sub ((I).integral (StoppedItoInputs.stop F μ H b (factor F μ H S hS hcontr M b u)))
      ((I).integral (StoppedItoInputs.stop F μ H a (factor F μ H S hS hcontr M b u)))] with ω hs ha hd
  rw [hs]
  simp only [Pi.add_apply,ha,hd,Pi.sub_apply]

end HeatMildRestart
#check @HeatMildRestart.past_kernel
#print axioms HeatMildRestart.past_kernel
#check @HeatMildRestart.map_constant
#print axioms HeatMildRestart.map_constant
#check @HeatMildRestart.restart
#print axioms HeatMildRestart.restart
#check @HeatMildRestart.conditional_mean
#print axioms HeatMildRestart.conditional_mean
