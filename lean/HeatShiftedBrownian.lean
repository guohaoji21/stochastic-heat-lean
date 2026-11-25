import HeatCanonicalNative
import SHE.NullCompleteFiltration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatShiftedBrownian
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

def filtration (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (a : ℝ≥0) : Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq := fun s => F (a+s)
  mono' := fun _ _ h => F.mono (add_le_add le_rfl h)
  le' := fun s => F.le (a+s)

def process (W : ℝ≥0 → Ω → ℝ) (a s : ℝ≥0) (ω : Ω) : ℝ := W (a+s) ω-W a ω

theorem filtered {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    (hW : IsFilteredPreBrownian W F μ) (a : ℝ≥0) :
    IsFilteredPreBrownian (process W a) (filtration F a) μ where
  toIsPreBrownianReal := hW.toIsPreBrownianReal.shift a
  stronglyAdapted := fun s => (hW.stronglyAdapted (a+s)).sub
    ((hW.stronglyAdapted a).mono (F.mono (le_add_of_nonneg_right (show (0:ℝ≥0) ≤ s from bot_le))))
  indep s t hst := by
    have he : process W a t-process W a s=(W (a+t)-W (a+s)) := by
      funext ω
      dsimp only [process,Pi.sub_apply]
      ring
    change Indep (MeasurableSpace.comap (process W a t-process W a s) inferInstance) (F (a+s)) μ
    rw [he]
    exact hW.indep (a+s) (a+t) (add_le_add le_rfl hst)

theorem continuous (W : ℝ≥0 → Ω → ℝ) (hWc : ∀ ω,Continuous (fun s => W s ω)) (a : ℝ≥0) :
    ∀ ω,Continuous (fun s => process W a s ω) := by
  intro ω
  exact ((hWc ω).comp (continuous_const.add continuous_id)).sub continuous_const

theorem contains_nulls {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω}
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (a : ℝ≥0) :
    NullCompleteFiltration.ContainsNullSets (filtration F a) μ :=
  fun s A hA => hnull (a+s) A hA

end HeatShiftedBrownian
#check @HeatShiftedBrownian.filtered
#print axioms HeatShiftedBrownian.filtered
#check @HeatShiftedBrownian.continuous
#print axioms HeatShiftedBrownian.continuous
#check @HeatShiftedBrownian.contains_nulls
#print axioms HeatShiftedBrownian.contains_nulls
