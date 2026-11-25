import HeatWeightedBrownian
import HeatStoppedMartingale

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatWeightedBrownianProcess
open MeasureTheory Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

def clock (a b t : ℝ≥0) : ℝ≥0 := min b (max a t)
def process (W : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (C : Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  C ω * (W (clock a b t) ω-W a ω)

theorem clock_mem {a b : ℝ≥0} (hab : a ≤ b) (t : ℝ≥0) : a ≤ clock a b t ∧ clock a b t ≤ b :=
  ⟨le_min hab (le_max_left _ _),min_le_left _ _⟩

theorem continuous (W : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => W t ω))
    (a b : ℝ≥0) (C : Ω → ℝ) (ω : Ω) : Continuous (fun t => process W a b C t ω) :=
  continuous_const.mul (((hc ω).comp (continuous_const.min (continuous_const.max continuous_id))).sub continuous_const)

theorem adapted (W : ℝ≥0 → Ω → ℝ) (hWa : ∀ t, StronglyMeasurable[F t] (W t))
    {a b : ℝ≥0} (hab : a ≤ b) (C : Ω → ℝ) (hC : StronglyMeasurable[F a] C) :
    StronglyAdapted F (process W a b C) := by
  intro t
  by_cases hat : a ≤ t
  · have hclock : clock a b t ≤ t := by unfold clock; rw [max_eq_right hat]; exact min_le_right _ _
    exact (hC.mono (F.mono hat)).mul
      (((hWa (clock a b t)).mono (F.mono hclock)).sub ((hWa a).mono (F.mono hat)))
  · have he : clock a b t = a := by unfold clock; rw [max_eq_left (le_of_not_ge hat),min_eq_right hab]
    have hz : process W a b C t = fun _ => 0 := by funext ω; simp [process,he]
    rw [hz]
    exact stronglyMeasurable_const

theorem stop_input {a b : ℝ≥0} (hab : a ≤ b) (C : Ω → ℝ)
    (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) (t : ℝ≥0) :
    StoppedItoInputs.stop F μ H t (HeatWeightedCellInput.constant F μ H a b C hC hCm (HeatTerminalBrownian.e ())) =
      HeatWeightedCellInput.constant F μ H a (clock a b t) C hC hCm (HeatTerminalBrownian.e ()) := by
  apply SHE.PastItoAlgebra.eq_of_ambient_ae
  have hn : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 ≠ t :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne t)
  filter_upwards [StoppedItoInputs.stop_ae F μ H t
    (HeatWeightedCellInput.constant F μ H a b C hC hCm (HeatTerminalBrownian.e ())),
    HeatWeightedCellInput.constant_ae F μ H a b C hC hCm (HeatTerminalBrownian.e ()),
    HeatWeightedCellInput.constant_ae F μ H a (clock a b t) C hC hCm (HeatTerminalBrownian.e ()),hn]
    with p hs hv hr hn
  rw [hs,hr]
  have hcond : (p.1 ∈ Ioc a (clock a b t)) ↔ (p.1 ∈ Ioc a b ∧ p.1 < t) := by
    simp only [clock,mem_Ioc,le_min_iff,le_max_iff]
    constructor
    · rintro ⟨ha,hb,hle | hle⟩
      · exact False.elim ((not_le_of_gt ha) hle)
      · exact ⟨⟨ha,hb⟩,lt_of_le_of_ne hle hn⟩
    · rintro ⟨⟨ha,hb⟩,ht⟩
      exact ⟨ha,hb,Or.inr ht.le⟩
  by_cases ht : p.1 < t <;> by_cases hm : p.1 ∈ Ioc a b
  · have hc := hcond.mpr ⟨hm,ht⟩
    rw [Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (t:ℝ) from ht),hv]
    simp [PredictableSteps.step,hm,hc]
  · have hc : p.1 ∉ Ioc a (clock a b t) := fun h => hm (hcond.mp h).1
    rw [Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (t:ℝ) from ht),hv]
    simp [PredictableSteps.step,hm,hc]
  · have hc : p.1 ∉ Ioc a (clock a b t) := fun h => ht (hcond.mp h).2
    rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (t:ℝ) from ht)]
    simp [PredictableSteps.step,hc]
  · have hc : p.1 ∉ Ioc a (clock a b t) := fun h => ht (hcond.mp h).2
    rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (t:ℝ) from ht)]
    simp [PredictableSteps.step,hc]

theorem represents (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    {a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H) (C : Ω → ℝ)
    (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) (t : ℝ≥0) :
    process W a b C t =ᵐ[μ] J.integral (StoppedItoInputs.stop F μ H t
      (HeatWeightedCellInput.constant F μ H a b C hC hCm (HeatTerminalBrownian.e ()))) := by
  rw [stop_input F μ H hab C hC hCm t]
  exact (HeatWeightedBrownian.weighted_integral F μ H J hlocal W hW (clock_mem hab t).1
    ((clock_mem hab t).2.trans hbH) C hC hCm).symm

theorem exists_envelope (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    (hWa : ∀ t, StronglyMeasurable[F t] (W t)) (hc : ∀ ω, Continuous (fun t => W t ω))
    {a b : ℝ≥0} (hab : a ≤ b) (hbH : b ≤ H) (C : Ω → ℝ)
    (hC : StronglyMeasurable[F a] C) (hCm : MemLp C 2 μ) :
    ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0 ≤ D ω) ∧
      ∀ t : ℝ≥0, t ≤ H → ∀ ω, ‖process W a b C t ω‖ ≤ D ω := by
  obtain ⟨D,hD,hD0,hDb,_⟩ := HeatStoppedMartingale.exists_envelope J hlocal
    (HeatWeightedCellInput.constant F μ H a b C hC hCm (HeatTerminalBrownian.e ()))
    (process W a b C) (adapted F W hWa hab C hC) (continuous W hc a b C)
    (represents F μ H J hlocal W hW hab hbH C hC hCm)
  exact ⟨D,hD,hD0,hDb⟩

end HeatWeightedBrownianProcess
#check @HeatWeightedBrownianProcess.clock_mem
#print axioms HeatWeightedBrownianProcess.clock_mem
#check @HeatWeightedBrownianProcess.continuous
#print axioms HeatWeightedBrownianProcess.continuous
#check @HeatWeightedBrownianProcess.adapted
#print axioms HeatWeightedBrownianProcess.adapted
#check @HeatWeightedBrownianProcess.stop_input
#print axioms HeatWeightedBrownianProcess.stop_input
#check @HeatWeightedBrownianProcess.represents
#print axioms HeatWeightedBrownianProcess.represents
#check @HeatWeightedBrownianProcess.exists_envelope
#print axioms HeatWeightedBrownianProcess.exists_envelope
