import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section
namespace HeatCompactLpBound
open MeasureTheory Set
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  (μ : Measure Ω) (H : ℝ≥0)

theorem exists_bound (V : ℝ≥0 → Lp E 2 μ) (hV : Continuous V) :
    ∃ C : ℝ, 0≤C ∧ ∀ t, t≤H → ‖V t‖≤C := by
  obtain ⟨t,ht,hmax⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ≥0) H)).exists_isMaxOn
    ⟨0,⟨le_rfl,zero_le⟩⟩ hV.norm.continuousOn
  exact ⟨‖V t‖,norm_nonneg _,fun s hs => hmax ⟨zero_le,hs⟩⟩

end HeatCompactLpBound
#check @HeatCompactLpBound.exists_bound
#print HeatCompactLpBound.exists_bound
#print axioms HeatCompactLpBound.exists_bound
