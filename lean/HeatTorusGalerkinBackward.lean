import HeatCanonicalBackwardEquation
import HeatAnalyticGalerkinEnergy
import HeatCountableBasis
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatTorusGalerkinBackward

open MeasureTheory SHE SHE.PredictableL2 UnitAddTorus
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

abbrev State (S : Finset (ι → ℤ)) := EuclideanSpace ℂ ↥S

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

private def indices (S : Finset (ι → ℤ)) : Set (State S) :=
  Classical.choose (HeatCountableBasis.exists_countable_hilbertBasis (E := State S))

private instance (S : Finset (ι → ℤ)) : Countable (indices S) :=
  (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis (E := State S))).1.to_subtype

def basis (S : Finset (ι → ℤ)) : HilbertBasis (indices S) ℝ (State S) :=
  Classical.choice (Classical.choose_spec (HeatCountableBasis.exists_countable_hilbertBasis (E := State S))).2

private def realMatrix (S : Finset (ι → ℤ)) (M : Matrix ↥S ↥S ℂ) : State S →L[ℝ] State S :=
  (Matrix.toEuclideanCLM (n := ↥S) (𝕜 := ℂ) M).restrictScalars ℝ

private theorem matrix_apply (S : Finset (ι → ℤ)) (M : Matrix ↥S ↥S ℂ) (x : State S) (k : ↥S) :
    realMatrix S M x k = ∑ l : ↥S, M k l * x l := by
  change (Matrix.toEuclideanCLM (n := ↥S) (𝕜 := ℂ) M x).ofLp k = _
  rw [Matrix.ofLp_toEuclideanCLM]
  rfl

/-- The torus heat generator restricted to the finite Fourier modes. -/
def laplace (S : Finset (ι → ℤ)) (P : ℝ) : State S →L[ℝ] State S := by
  classical
  exact realMatrix S (Matrix.diagonal fun k => ((-HeatTorusFourier.frequencySquared P k.val : ℝ) : ℂ))

/-- Fourier multiplication by the coefficient followed by projection back
to the same finite frequency set. -/
def multiplier (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) : State S →L[ℝ] State S :=
  realMatrix S (fun k l => mFourierCoeff b (k.val - l.val))

theorem laplace_apply (S : Finset (ι → ℤ)) (P : ℝ) (x : State S) (k : ↥S) :
    laplace S P x k = ((-HeatTorusFourier.frequencySquared P k.val : ℝ) : ℂ) * x k := by
  classical
  unfold laplace
  rw [matrix_apply]
  simp [Matrix.diagonal_apply]

theorem multiplier_apply (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) (x : State S) (k : ↥S) :
    multiplier S b x k = ∑ l : ↥S, mFourierCoeff b (k.val - l.val) * x l :=
  matrix_apply S _ x k

/-- The orthogonal coordinate projection onto one complex Fourier mode, as
a real-linear map on the Galerkin space. -/
def modeProjection (S : Finset (ι → ℤ)) (k : ↥S) : State S →L[ℝ] State S := by
  classical
  exact realMatrix S (Matrix.diagonal fun l => if l = k then (1 : ℂ) else 0)

private theorem projection_apply (S : Finset (ι → ℤ)) (k l : ↥S) (x : State S) :
    modeProjection S k x l = if l = k then x l else 0 := by
  classical
  unfold modeProjection
  rw [matrix_apply]
  simp [Matrix.diagonal_apply, ite_mul]

private theorem projection_single (S : Finset (ι → ℤ)) (k : ↥S) (x : State S) :
    modeProjection S k x = EuclideanSpace.single k (x k) := by
  classical
  ext l
  rw [projection_apply, PiLp.single_apply]
  by_cases h : l = k
  · subst l
    simp
  · simp [h, Ne.symm h]

theorem modeProjection_norm_sq (S : Finset (ι → ℤ)) (k : ↥S) (x : State S) :
    ‖modeProjection S k x‖ ^ 2 = ‖x k‖ ^ 2 := by
  classical
  rw [projection_single, PiLp.norm_single]

theorem modeProjection_inner (S : Finset (ι → ℤ)) (k : ↥S) (x y : State S) :
    inner ℝ (modeProjection S k x) (modeProjection S k y) = (x k * star (y k)).re := by
  classical
  rw [real_inner_comm, projection_single S k x]
  change (inner ℂ (modeProjection S k y) (EuclideanSpace.single k (x k))).re = _
  rw [EuclideanSpace.inner_single_right, projection_apply, ite_eq_left rfl]
  rfl

/-- The Galerkin noise matrix is the projection of the actual spatial
product in the original Haar Fourier coordinates. -/
theorem coefficient_mul (S : Finset (ι → ℤ)) (b : C(UnitAddTorus ι, ℂ)) (x : State S) (k : ↥S) :
    mFourierCoeff (fun z => b z * ∑ l : ↥S, x l * mFourier l.val z) k.val =
      multiplier S b x k := by
  classical
  let y (l : ι → ℤ) : ℂ := if hl : l ∈ S then x ⟨l, hl⟩ else 0
  have hy (l : ↥S) : y l.val = x l := by simp [y]
  have hsum (z : UnitAddTorus ι) :
      (∑ l : ↥S, x l * mFourier l.val z) = ∑ l ∈ S, y l * mFourier l z := by
    rw [← Finset.sum_coe_sort S (fun l => y l * mFourier l z)]
    simp only [hy]
  simp_rw [hsum]
  rw [HeatAnalyticGalerkinEnergy.coefficient_mul_polynomial, multiplier_apply, ← Finset.sum_coe_sort]
  simp only [hy]

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace C(ℝ≥0, ℝ) :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (HilbertColumns.Space Unit ℝ) := borel _
local instance : BorelSpace (HilbertColumns.Space Unit ℝ) := ⟨rfl⟩

/-- The finite Fourier Galerkin backward equation with its actual heat and
multiplicative-noise matrices on canonical Wiener space. -/
theorem exists_solution (S : Finset (ι → ℤ)) (P : ℝ) (b : C(UnitAddTorus ι, ℂ)) (H : ℝ≥0)
    (η : Lp (State S) 2 μ) (hη : AEStronglyMeasurable[F H] (η : C(ℝ≥0, ℝ) → State S) μ) :
    Nonempty (HeatLocalBackwardEquation.Solution
      (HeatTerminalNaturality.integral F μ H (basis S) (HeatCanonicalNative.scalar H))
      (laplace S P) (multiplier S b) 0 H η) :=
  HeatCanonicalBackwardEquation.exists_solution H (basis S) (laplace S P) (multiplier S b) η hη

end HeatTorusGalerkinBackward

#print axioms HeatTorusGalerkinBackward.coefficient_mul
#print axioms HeatTorusGalerkinBackward.exists_solution
