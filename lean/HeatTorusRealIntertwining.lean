import HeatTorusReal
import HeatTorusControlObservation
import HeatRestrictionAdjoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusRealIntertwining

open Filter MeasureTheory UnitAddTorus HeatTorusReal HeatTorusFourier
open HeatTorusGalerkinCompression (fullMultiplier fullMultiplier_ae)

variable {ι : Type*} [Fintype ι]
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local notation "Haar" => (volume : Measure (UnitAddTorus ι))
local notation "Full" => State ι

private def imagPart : Full →L[ℝ] RealState ι := Complex.imCLM.compLpL 2 Haar

private theorem real_imag_decomposition (x : Full) :
    embed (realPart x) + Complex.I • embed (imagPart x) = x := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (embed (realPart x)) (Complex.I • embed (imagPart x)),
    Lp.coeFn_smul Complex.I (embed (imagPart x)), embed_ae (realPart x), realPart_ae x,
    embed_ae (imagPart x), Complex.imCLM.coeFn_compLpL x] with p h₁ h₂ h₃ h₄ h₅ h₆
  change imagPart x p = (x p).im at h₆
  rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, h₃, h₄, h₅, h₆, smul_eq_mul, mul_comm Complex.I]
  exact Complex.re_add_im (x p)

private theorem realPart_imaginary (y : RealState ι) : realPart (Complex.I • embed y) = 0 := by
  apply Lp.ext
  filter_upwards [realPart_ae (Complex.I • embed y), Lp.coeFn_smul Complex.I (embed y),
    embed_ae y, Lp.coeFn_zero ℝ 2 Haar] with p h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply, h₃, h₄]
  simp [smul_eq_mul, Complex.mul_re]

theorem heat_commutes (P t : ℝ) (x : Full) :
    realPart (heat P t x) = realHeat P t (realPart x) := by
  calc
    realPart (heat P t x) =
        realPart (heat P t (embed (realPart x) + Complex.I • embed (imagPart x))) :=
      congrArg (fun z : Full => realPart (heat P t z)) (real_imag_decomposition x).symm
    _ = realHeat P t (realPart x) := by
      rw [map_add, map_smul, ← embed_realHeat, ← embed_realHeat, map_add,
        realPart_embed, realPart_imaginary, add_zero]

/-- The real multiplication operator by the real part of the same bounded coefficient. -/
def multiplier (b : C(UnitAddTorus ι, ℂ)) : RealState ι →L[ℝ] RealState ι :=
  realPart.comp ((fullMultiplier b).comp embed)

theorem multiplier_ae (b : C(UnitAddTorus ι, ℂ)) (v : RealState ι) :
    (multiplier b v : UnitAddTorus ι → ℝ) =ᵐ[Haar] fun x => (b x).re * v x := by
  filter_upwards [realPart_ae (fullMultiplier b (embed v)), fullMultiplier_ae b (embed v),
    embed_ae v] with x h₁ h₂ h₃
  change realPart (fullMultiplier b (embed v)) x = _
  rw [h₁, h₂, h₃]
  simp [Complex.mul_re]

theorem multiplier_commutes (b : C(UnitAddTorus ι, ℂ)) (hb : ∀ x, (b x).im = 0) (x : Full) :
    realPart (fullMultiplier b x) = multiplier b (realPart x) := by
  apply Lp.ext
  filter_upwards [realPart_ae (fullMultiplier b x), fullMultiplier_ae b x,
    multiplier_ae b (realPart x), realPart_ae x] with p h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  simp [Complex.mul_re, hb p]

abbrev Local (O : Set (UnitAddTorus ι)) := Lp ℝ 2 (Measure.restrict Haar O)

def localRealPart (O : Set (UnitAddTorus ι)) : HeatTorusControlObservation.Control O →L[ℝ] Local O :=
  Complex.reCLM.compLpL 2 (Measure.restrict Haar O)

theorem extension_commutes {O : Set (UnitAddTorus ι)} (hO : MeasurableSet O)
    (u : HeatTorusControlObservation.Control O) :
    realPart (HeatTorusControlObservation.extension O u) =
      HeatRestrictionAdjoint.adjointExtension Haar O (localRealPart O u) := by
  apply Lp.ext
  filter_upwards [realPart_ae (HeatTorusControlObservation.extension O u),
    HeatTorusControlObservation.extension_ae hO u,
    HeatRestrictionAdjoint.adjointExtension_ae Haar O hO (localRealPart O u),
    (ae_restrict_iff' hO).mp (Complex.reCLM.coeFn_compLpL u)] with p h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃]
  by_cases hp : p ∈ O
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    exact (show localRealPart O u p = (u p).re from h₄ hp).symm
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, Complex.zero_re]

end HeatTorusRealIntertwining

#print axioms HeatTorusRealIntertwining.heat_commutes
#print axioms HeatTorusRealIntertwining.multiplier_commutes
#print axioms HeatTorusRealIntertwining.extension_commutes
