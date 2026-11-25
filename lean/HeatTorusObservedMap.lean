import HeatTorusObservedPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace HeatTorusObservedMap

open Filter MeasureTheory Set UnitAddTorus SHE.PredictableL2
open HeatTorusGalerkinBackward (State)
open HeatTorusObservedPolynomial (coordinate polynomial observedEnergy)
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : Finset (ι → ℤ)}

local instance : InnerProductSpace ℝ (Lp ℂ 2 μ) :=
  InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 μ)

private def polynomialMap : Lp (State S) 2 μ →ₗ[ℂ] C(UnitAddTorus ι, Lp ℂ 2 μ) where
  toFun X := polynomial (coordinate X)
  map_add' X Y := by
    apply ContinuousMap.ext
    intro x
    change (∑ k : ↥S, mFourier k.val x • coordinate (X + Y) k) =
      (∑ k : ↥S, mFourier k.val x • coordinate X k) + (∑ k : ↥S, mFourier k.val x • coordinate Y k)
    simp only [coordinate, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    apply ContinuousMap.ext
    intro x
    simp only [RingHom.id_apply, ContinuousMap.smul_apply]
    change (∑ k : ↥S, mFourier k.val x • coordinate (z • X) k) =
      z • (∑ k : ↥S, mFourier k.val x • coordinate X k)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [coordinate, map_smul]
    exact smul_comm _ _ _

private def linear (O : Set (UnitAddTorus ι)) :
    Lp (State S) 2 μ →ₗ[ℂ] Lp (Lp ℂ 2 μ) 2 (volume.restrict O) :=
  (ContinuousMap.toLp 2 (volume.restrict O) ℂ).toLinearMap.comp polynomialMap

private theorem linear_norm_sq (O : Set (UnitAddTorus ι)) (X : Lp (State S) 2 μ) :
    ‖linear O X‖ ^ 2 = observedEnergy O X := by
  change ‖ContinuousMap.toLp 2 (volume.restrict O) ℂ (polynomial (coordinate X))‖ ^ 2 = _
  rw [realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume.restrict O)
    (polynomial (coordinate X))] with x hx
  exact congrArg (fun y : Lp ℂ 2 μ => ‖y‖ ^ 2) hx

theorem energy_le (O : Set (UnitAddTorus ι)) (X : Lp (State S) 2 μ) :
    observedEnergy O X ≤ ‖X‖ ^ 2 := by
  rw [← HeatTorusObservedPolynomial.global_energy X]
  exact setIntegral_le_integral (HeatTorusObservedPolynomial.memLp (coordinate X)).norm.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)

/-- Restriction of the actual random Galerkin polynomial to the observation
set, with operator bound one in the normalized Haar norms. -/
def observe (O : Set (UnitAddTorus ι)) :
    Lp (State S) 2 μ →L[ℂ] Lp (Lp ℂ 2 μ) 2 (volume.restrict O) :=
  (linear O).mkContinuous 1 fun X => by
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), linear_norm_sq]
    exact energy_le O X

theorem observe_norm_sq (O : Set (UnitAddTorus ι)) (X : Lp (State S) 2 μ) :
    ‖observe O X‖ ^ 2 = observedEnergy O X := linear_norm_sq O X

theorem integrable_energy {T : Type*} [MeasurableSpace T] {ν : Measure T}
    (O : Set (UnitAddTorus ι)) {X : T → Lp (State S) 2 μ} (hX : MemLp X 2 ν) :
    Integrable (fun t => observedEnergy O (X t)) ν := by
  apply hX.norm.integrable_sq.mono'
    ((show Continuous (fun Y : Lp (State S) 2 μ => observedEnergy O Y) by
      simp_rw [← observe_norm_sq]
      exact (ContinuousLinearMap.continuous _).norm.pow 2).comp_aestronglyMeasurable hX.aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  rw [← observe_norm_sq, Real.norm_of_nonneg (sq_nonneg _), observe_norm_sq]
  exact energy_le O (X t)

end HeatTorusObservedMap

#print axioms HeatTorusObservedMap.observe_norm_sq
#print axioms HeatTorusObservedMap.integrable_energy
