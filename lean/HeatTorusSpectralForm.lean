import HeatTorusGalerkinProjection
import HeatTorusSobolevForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusSpectralForm

open Filter MeasureTheory UnitAddTorus HeatTorusFourier HeatTorusGradient
open HeatTorusGalerkinBackward (laplace laplace_apply)
open HeatTorusGalerkinProjection (analysis synthesis project coefficient_synthesis coefficient_project)
open scoped ENNReal Topology ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

/-- The Fourier projections preserve weak derivatives. -/
theorem project_gradient (P : ℝ) (S : Finset (ι → ℤ)) (u : State ι) (D : ι → State ι)
    (hD : HasGradient P u D) :
    HasGradient P (project S u) (fun i => project S (D i)) := by
  classical
  intro i k
  rw [coefficient_project, coefficient_project, hD i k]
  by_cases h : k ∈ S <;> simp [h]

/-- Trigonometric polynomials approximate every Sobolev state together with
all its weak derivatives. -/
theorem graph_tendsto (P : ℝ) (u : State ι) (D : ι → State ι) (hD : HasGradient P u D) :
    Tendsto (fun S : Finset (ι → ℤ) => (project S u, fun i => project S (D i)))
      atTop (𝓝 (u, D)) ∧
        ∀ S : Finset (ι → ℤ), HasGradient P (project S u) (fun i => project S (D i)) := by
  refine ⟨(HeatTorusGalerkinProjection.project_tendsto u).prodMk_nhds
    (tendsto_pi_nhds.mpr (fun i => HeatTorusGalerkinProjection.project_tendsto (D i))), ?_⟩
  exact fun S => project_gradient P S u D hD

theorem synthesis_generator (P : ℝ) (S : Finset (ι → ℤ)) (z : HeatTorusGalerkinProjection.Finite S) :
    HasDerivWithinAt (fun t : ℝ => heat P t (synthesis S z))
      (synthesis S (laplace S P z)) (Set.Ici 0) 0 := by
  classical
  apply (generator_iff_coefficients P _ _).mpr
  intro k
  rw [coefficient_synthesis, coefficient_synthesis]
  by_cases h : k ∈ S
  · simp only [h, dite_eq_left, laplace_apply]
  · simp [h]

private theorem laplace_symmetric (P : ℝ) (S : Finset (ι → ℤ)) (x y : HeatTorusGalerkinProjection.Finite S) :
    inner ℂ x (laplace S P y) = inner ℂ (laplace S P x) y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  let a : ℂ := ((-frequencySquared P k.val : ℝ) : ℂ)
  have hx : laplace S P x k = a * x k := laplace_apply S P x k
  have hy : laplace S P y k = a * y k := laplace_apply S P y k
  change laplace S P y k * star (x k) = y k * star (laplace S P x k)
  calc
    _ = (a * y k) * star (x k) := congrArg (fun z : ℂ => z * star (x k)) hy
    _ = y k * star (a * x k) := by
      have ha : star a = a := Complex.conj_ofReal _
      rw [star_mul, ha]
      ring
    _ = _ := congrArg (fun z : ℂ => y k * star z) hx.symm

/-- On every polynomial test, the projected heat drift is exactly the
negative Sobolev gradient form for the unprojected state. -/
theorem weak_form (P : ℝ) (S : Finset (ι → ℤ)) (z : HeatTorusGalerkinProjection.Finite S) (u : State ι)
    (D E : ι → State ι) (hD : HasGradient P u D) (hE : HasGradient P (synthesis S z) E) :
    inner ℂ z (laplace S P (analysis S u)) = -∑ i, inner ℂ (E i) (D i) := by
  rw [laplace_symmetric]
  have h := (synthesis S).adjoint_inner_right (laplace S P z) u
  change inner ℂ (laplace S P z) (analysis S u) = inner ℂ (synthesis S (laplace S P z)) u at h
  rw [h]
  exact generator_inner_eq_gradient P _ _ _ E D (synthesis_generator P S z) hE hD

end HeatTorusSpectralForm

#print axioms HeatTorusSpectralForm.graph_tendsto
#print axioms HeatTorusSpectralForm.weak_form
