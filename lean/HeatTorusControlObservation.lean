import HeatTorusObservedMap
import HeatTorusGalerkinCompression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatTorusControlObservation

open Filter MeasureTheory Set UnitAddTorus SHE.PredictableL2
open HeatTorusGalerkinBackward (State)
open HeatTorusGalerkinProjection (synthesis analysis)
open HeatTorusObservedPolynomial (observedEnergy)
open scoped NNReal ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι]

abbrev Control (O : Set (UnitAddTorus ι)) :=
  Lp ℂ 2 ((volume : Measure (UnitAddTorus ι)).restrict O)

local notation "Full" => HeatTorusFourier.State ι
local notation "Haar" => (volume : Measure (UnitAddTorus ι))

private def restrictLinear (O : Set (UnitAddTorus ι)) : Full →ₗ[ℂ] Control O where
  toFun f := ((Lp.memLp f).restrict O).toLp f
  map_add' f g := Lp_toLp_restrict_add f g O
  map_smul' c f := Lp_toLp_restrict_smul c f O

/-- Restrict the full state to the actual local control region. -/
def restriction (O : Set (UnitAddTorus ι)) : Full →L[ℂ] Control O :=
  (restrictLinear O).mkContinuous 1 fun f => by
    change ‖((Lp.memLp f).restrict O).toLp f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_Lp_toLp_restrict_le O f

theorem restriction_ae (O : Set (UnitAddTorus ι)) (f : Full) :
    (restriction O f : UnitAddTorus ι → ℂ) =ᵐ[(Measure.restrict Haar O)] f :=
  ((Lp.memLp f).restrict O).coeFn_toLp

def extension (O : Set (UnitAddTorus ι)) : Control O →L[ℂ] Full := (restriction O).adjoint

/-- The adjoint of spatial restriction is zero extension for the same Haar measure. -/
theorem extension_ae {O : Set (UnitAddTorus ι)} (hO : MeasurableSet O) (g : Control O) :
    (extension O g : UnitAddTorus ι → ℂ) =ᵐ[Haar] O.indicator g := by
  have hm : MemLp (O.indicator g) 2 Haar :=
    (memLp_indicator_iff_restrict hO.nullMeasurableSet).2 (Lp.memLp g)
  let z : Full := hm.toLp _
  have he : extension O g = z := by
    apply ext_inner_left ℂ
    intro x
    change inner ℂ x ((restriction O).adjoint g) = inner ℂ x z
    rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def, ← integral_indicator hO]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' hO).mp (restriction_ae O x), hm.coeFn_toLp] with p hx hz
    by_cases hp : p ∈ O
    · rw [indicator_of_mem hp, hx hp, hz, indicator_of_mem hp]
    · rw [indicator_of_notMem hp, hz, indicator_of_notMem hp, inner_zero_right]
  rw [he]
  exact hm.coeFn_toLp

/-- The observation and the injection on the finite state space, with
the same control space as the full equation. -/
def observe (S : Finset (ι → ℤ)) (O : Set (UnitAddTorus ι)) : State S →L[ℝ] Control O :=
  ((restriction O).comp (synthesis S)).restrictScalars ℝ

def inject (S : Finset (ι → ℤ)) (O : Set (UnitAddTorus ι)) : Control O →L[ℝ] State S :=
  ((analysis S).comp (extension O)).restrictScalars ℝ

local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)

private theorem control_inner_re (O : Set (UnitAddTorus ι)) (u v : Control O) :
    inner ℝ u v = (inner ℂ u v).re := by
  rw [L2.inner_def, L2.inner_def]
  exact Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) u v)

theorem inject_inner (S : Finset (ι → ℤ)) (O : Set (UnitAddTorus ι)) (u : Control O) (z : State S) :
    inner ℝ (inject S O u) z = inner ℝ u (observe S O z) := by
  rw [control_inner_re]
  change (inner ℂ (analysis S (extension O u)) z).re =
    (inner ℂ u (restriction O (synthesis S z))).re
  rw [show analysis S = (synthesis S).adjoint from rfl,
    ContinuousLinearMap.adjoint_inner_left, show extension O = (restriction O).adjoint from rfl,
    ContinuousLinearMap.adjoint_inner_left]

private theorem observe_ae (S : Finset (ι → ℤ)) (O : Set (UnitAddTorus ι)) (x : State S) :
    (observe S O x : UnitAddTorus ι → ℂ) =ᵐ[(Measure.restrict Haar O)]
      fun p => ∑ k : ↥S, mFourier k.val p * x k :=
  (restriction_ae O (synthesis S x)).trans (ae_mono Measure.restrict_le_self
    ((HeatTorusGalerkinCompression.synthesis_ae S x).trans
      (Eventually.of_forall fun _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _)))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]

/-- The spectral observation energy is the mean square of the restriction
in the actual spatial control space. -/
theorem observation_norm_sq (S : Finset (ι → ℤ)) (O : Set (UnitAddTorus ι))
    (X : Lp (State S) 2 μ) :
    ‖((observe S O).compLpL 2 μ) X‖ ^ 2 = observedEnergy O X := by
  classical
  let e (p : Ω × UnitAddTorus ι) : ℝ := ‖∑ k : ↥S, mFourier k.val p.2 * X p.1 k‖ ^ 2
  let obs := observe S O
  let Y := (obs.compLpL 2 μ) X
  have hm (k : ↥S) : Measurable (fun p : Ω × UnitAddTorus ι => mFourier k.val p.2 * X p.1 k) :=
    ((mFourier k.val).continuous.measurable.comp measurable_snd).mul
      (((EuclideanSpace.proj (𝕜 := ℂ) k).continuous.comp_stronglyMeasurable
        (Lp.stronglyMeasurable X)).measurable.comp measurable_fst)
  have he : Measurable e := (Finset.measurable_sum _ fun k _ => hm k).norm.pow_const 2
  have hi (ω : Ω) : (fun p => e (ω, p)) =ᵐ[(Measure.restrict Haar O)] fun p => ‖obs (X ω) p‖ ^ 2 :=
    ((observe_ae S O (X ω)).fun_comp (fun z : ℂ => ‖z‖ ^ 2)).symm
  have hnorm (ω : Ω) : (∫ p, e (ω, p) ∂(Measure.restrict Haar O)) = ‖obs (X ω)‖ ^ 2 := by
    rw [realLp_norm_sq]
    exact integral_congr_ae (hi ω)
  have hY : (fun ω => ∫ p, e (ω, p) ∂(Measure.restrict Haar O)) =ᵐ[μ] fun ω => ‖Y ω‖ ^ 2 := by
    filter_upwards [obs.coeFn_compLpL X] with ω hω
    rw [hnorm, hω]
  have hei : Integrable e (μ.prod ((Measure.restrict Haar O))) := by
    apply (integrable_prod_iff he.stronglyMeasurable.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun ω => (Lp.memLp (obs (X ω))).norm.integrable_sq.congr
      (hi ω).symm, ?_⟩
    apply (Lp.memLp Y).norm.integrable_sq.congr
    filter_upwards [hY] with ω hω
    simpa only [e, Real.norm_of_nonneg (sq_nonneg _)] using hω.symm
  rw [HeatTorusObservedPolynomial.observedEnergy_eq_integral, realLp_norm_sq]
  calc
    _ = ∫ ω, ∫ p, e (ω, p) ∂(Measure.restrict Haar O) ∂μ := integral_congr_ae hY.symm
    _ = ∫ p, ∫ ω, e (ω, p) ∂μ ∂(Measure.restrict Haar O) := integral_integral_swap hei
    _ = _ := rfl

end HeatTorusControlObservation

#print axioms HeatTorusControlObservation.extension_ae
#print axioms HeatTorusControlObservation.inject_inner
#print axioms HeatTorusControlObservation.observation_norm_sq
