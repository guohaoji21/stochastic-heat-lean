import HeatTorusUniformTail
import HeatTerminalNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace HeatTorusLiftedProjection

open Filter MeasureTheory UnitAddTorus
open HeatTorusGalerkinBackward (State)
open HeatTorusGalerkinProjection (analysis synthesis project)
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local notation "Full" => HeatTorusFourier.State ι
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)

/-- Fourier analysis on the space of square-integrable random states. -/
def analyze (S : Finset (ι → ℤ)) : Lp Full 2 μ →L[ℝ] Lp (State S) 2 μ :=
  ((analysis S).restrictScalars ℝ).compLpL 2 μ

theorem analyze_ae (S : Finset (ι → ℤ)) (x : Lp Full 2 μ) :
    (analyze μ S x : Ω → State S) =ᵐ[μ] fun ω => analysis S (x ω) :=
  ((analysis S).restrictScalars ℝ).coeFn_compLpL x

private theorem full_inner_re (x y : Full) : inner ℝ x y = (inner ℂ x y).re := by
  rw [L2.inner_def, L2.inner_def]
  exact Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) x y)

private theorem analyze_inner_spatial (S : Finset (ι → ℤ)) (x : Full) (z : State S) :
    inner ℝ (analysis S x) z = inner ℝ x (synthesis S z) := by
  rw [full_inner_re]
  change (inner ℂ (analysis S x) z).re = (inner ℂ x (synthesis S z)).re
  exact congrArg Complex.re ((synthesis S).adjoint_inner_left z x)

theorem analyze_norm_le (S : Finset (ι → ℤ)) (x : Lp Full 2 μ) :
    ‖analyze μ S x‖ ≤ ‖x‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [analyze_ae μ S x] with ω h
  change ‖analyze μ S x ω‖ ≤ ‖x ω‖
  rw [h]
  exact HeatTorusGalerkinProjection.analysis_contraction S (x ω)

theorem analyze_const [IsFiniteMeasure μ] (S : Finset (ι → ℤ)) (g : Full) :
    analyze μ S (Lp.const 2 μ g) = Lp.const 2 μ (analysis S g) := by
  apply Lp.ext
  filter_upwards [analyze_ae μ S (Lp.const 2 μ g),
    Lp.coeFn_const 2 μ g, Lp.coeFn_const 2 μ (analysis S g)] with ω h₁ h₂ h₃
  change analyze μ S (Lp.const 2 μ g) ω = (Lp.const 2 μ (analysis S g)) ω
  rw [h₁, h₂, h₃]
  rfl

theorem analyze_adapted {m : MeasurableSpace Ω} (S : Finset (ι → ℤ)) (x : Lp Full 2 μ)
    (hx : AEStronglyMeasurable[m] (x : Ω → Full) μ) :
    AEStronglyMeasurable[m] (@analyze ι _ Ω mΩ μ S x : Ω → State S) μ :=
  ((analysis S).continuous.comp_aestronglyMeasurable hx).congr
    (@analyze_ae ι _ Ω mΩ μ S x).symm

/-- Testing both projected fields is equivalent to projecting only the
test field in the full Hilbert space. -/
theorem analyze_inner (S : Finset (ι → ℤ)) (x y : Lp Full 2 μ) :
    inner ℝ (analyze μ S x) (analyze μ S y) = inner ℝ x (((project S).compLpL 2 μ) y) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [analyze_ae μ S x, analyze_ae μ S y, (project S).coeFn_compLpL y]
    with ω hx hy hp
  change inner ℝ (analyze μ S x ω) (analyze μ S y ω) =
    inner ℝ (x ω) (((project S).compLpL 2 μ) y ω)
  rw [hx, hy, hp]
  exact analyze_inner_spatial S (x ω) (analysis S (y ω))

theorem lifted_tail_eq (n : ℕ) (x : Lp Full 2 μ) :
    ((HeatTorusUniformTail.tail (ι := ι) n).compLpL 2 μ) x =
      x - ((project (HeatTorusFrequencyExhaustion.box ι n)).compLpL 2 μ) x := by
  let P := project (HeatTorusFrequencyExhaustion.box ι n)
  apply Lp.ext
  filter_upwards [(HeatTorusUniformTail.tail (ι := ι) n).coeFn_compLpL x, P.coeFn_compLpL x,
    Lp.coeFn_sub x ((P.compLpL 2 μ) x)] with ω hl hp hs
  rw [hl, hs, Pi.sub_apply, hp]
  rfl

end HeatTorusLiftedProjection

#print axioms HeatTorusLiftedProjection.analyze_inner
#print axioms HeatTorusLiftedProjection.lifted_tail_eq
