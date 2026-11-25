import HeatTorusDirichletMass
import HeatTorusSmoothWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatTorusDirichletBall

open Filter MeasureTheory Set UnitAddTorus
open HeatTorusReal HeatTorusPatchSobolev HeatTorusFundamentalCell HeatTorusDirichletMass
open HeatFlatTorusSmoothLift (covering)
open HeatRestrictionAdjoint (adjointExtension adjointExtension_ae)
open HeatTorusSmoothWeight (weight weight_ae)
open scoped RealInnerProductSpace NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {d : ℕ}

def cellOrigin (c : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ := c i - 1 / 2

theorem ball_subset_cell (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : r < 1 / 2) :
    Metric.ball c r ⊆ cell (cellOrigin c) :=
  Metric.ball_subset_closedBall.trans (closedBall_subset_cell c hr)

theorem measurable_image_ball (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : r < 1 / 2) :
    MeasurableSet (covering 1 '' Metric.ball c r) := by
  let a := cellOrigin c
  have he : covering 1 '' Metric.ball c r = representative a ⁻¹' Metric.ball c r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change representative a (covering 1 y) ∈ Metric.ball c r
      rwa [representative_covering a (ball_subset_cell c hr hy)]
    · intro hx
      exact ⟨representative a x, hx, covering_representative a x⟩
  rw [he]
  exact measurableSet_ball.preimage (measurable_representative a)

private theorem multiplier_fixes_ball_extension (c : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hr : r < 1 / 2) (b : C(UnitAddTorus (Fin d), ℝ))
    (hb : ∀ x ∈ covering 1 '' Metric.ball c r, b x = 1)
    (f : PatchState (Metric.ball c r)) :
    weight b (adjointExtension volume (covering 1 '' Metric.ball c r) f) =
      adjointExtension volume (covering 1 '' Metric.ball c r) f := by
  let S := covering 1 '' Metric.ball c r
  let F := adjointExtension volume S f
  apply Lp.ext
  filter_upwards [weight_ae b F, adjointExtension_ae volume S (measurable_image_ball c hr) f]
    with x hx hf
  by_cases hs : x ∈ S
  · rw [hx, hb x hs, one_mul]
  · rw [hx, hf, indicator_of_notMem hs, mul_zero]

/-- The paper's positive initial-pairing lower bound for an embedded
coordinate ball on which the noise multiplier is one. -/
theorem initial_pairing_ball (P : ℝ) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : r < 1 / 2)
    (b : C(UnitAddTorus (Fin d), ℝ)) (hb : ∀ x, 0 ≤ b x)
    (hplateau : ∀ x ∈ covering 1 '' Metric.ball c r, b x = 1)
    (h : ℕ → ℝ≥0) (N : ℕ) (T : ℝ≥0) (hT : ∑ k ∈ Finset.range N, h (N - k) = T)
    (g : RealState (Fin d)) (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (hg₀ : g ≠ 0)
    (hsupp : ∀ᵐ x ∂volume, x ∉ covering 1 '' Metric.ball c r → g x = 0) :
    let cT := ‖HeatSmallDomainDirichletHeat.heat Metric.isOpen_ball Metric.isBounded_ball
          ((T / 2) / Real.toNNReal (P ^ 2))
          (pull (cellOrigin c) (ball_subset_cell c hr) (measurable_image_ball c hr) g)‖ ^ 2
    0 < cT ∧ cT ≤ ⟪g, HeatBackwardChain.stateAt (HeatTorusCovarianceSeparation.K P (weight b)) h N g 0⟫ := by
  have hpos : HeatTorusMass.Positive (weight b) := by
    intro u hu
    filter_upwards [weight_ae b u, hu] with x hx hy
    rw [hx]
    exact mul_nonneg (hb x) hy
  exact initial_pairing_dirichlet (cellOrigin c) (ball_subset_cell c hr) (measurable_image_ball c hr)
    Metric.isOpen_ball Metric.isBounded_ball P (weight b) hpos
    (multiplier_fixes_ball_extension c hr b hplateau) h N T hT g hg hg₀ hsupp

end HeatTorusDirichletBall

#print axioms HeatTorusDirichletBall.measurable_image_ball
#print axioms HeatTorusDirichletBall.initial_pairing_ball
