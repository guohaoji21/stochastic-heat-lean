import HeatTorusSobolevFourier

set_option autoImplicit false
noncomputable section

namespace HeatTorusSobolevForm

open MeasureTheory Set UnitAddTorus HeatTorusFourier HeatTorusGradient
open scoped ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

/-- The Sobolev graph is closed in the product of the state and gradient spaces. -/
theorem isClosed_graph (P : ℝ) :
    IsClosed {x : State ι × (ι → State ι) | HasGradient P x.1 x.2} := by
  have h : {x : State ι × (ι → State ι) | HasGradient P x.1 x.2} =
      ⋂ i : ι, ⋂ k : ι → ℤ,
        {x : State ι × (ι → State ι) | coefficientCLM k (x.2 i) = symbol P i k * coefficientCLM k x.1} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, HasGradient, coefficientCLM_apply]
  rw [h]
  refine isClosed_iInter (fun i => isClosed_iInter (fun k => isClosed_eq ?_ ?_))
  · exact (coefficientCLM k).continuous.comp ((continuous_apply i).comp continuous_snd)
  · exact continuous_const.mul ((coefficientCLM k).continuous.comp continuous_fst)

theorem gradient_unique (P : ℝ) (u : State ι) {D E : ι → State ι}
    (hD : HasGradient P u D) (hE : HasGradient P u E) : D = E := by
  funext i
  apply (mFourierBasis (d := ι)).repr.injective
  ext k
  simp only [mFourierBasis_repr, hD i k, hE i k]

private theorem coefficient_inner (u v : State ι) :
    inner ℂ u v = ∑' k : ι → ℤ, inner ℂ (mFourierCoeff u k) (mFourierCoeff v k) := by
  rw [← (mFourierBasis (d := ι)).repr.inner_map_map u v, lp.inner_eq_tsum]
  simp only [mFourierBasis_repr]

/-- Fourier derivatives satisfy weak spatial integration by parts. -/
theorem integration_by_parts (P : ℝ) (u v : State ι) (Du Dv : ι → State ι)
    (hu : HasGradient P u Du) (hv : HasGradient P v Dv) (i : ι) :
    inner ℂ (Du i) v = -inner ℂ u (Dv i) := by
  rw [coefficient_inner, coefficient_inner u, ← tsum_neg]
  apply tsum_congr
  intro k
  rw [hu i k, hv i k]
  change mFourierCoeff v k * star (symbol P i k * mFourierCoeff u k) =
    -((symbol P i k * mFourierCoeff v k) * star (mFourierCoeff u k))
  have hsymbol : star (symbol P i k) = -(symbol P i k) := by
    simp [symbol, Complex.star_def, map_mul, Complex.conj_ofReal]
  rw [star_mul, hsymbol]
  ring

end HeatTorusSobolevForm

#print axioms HeatTorusSobolevForm.isClosed_graph
#print axioms HeatTorusSobolevForm.gradient_unique
#print axioms HeatTorusSobolevForm.integration_by_parts
