import HeatTorusRealCoordinates
import HeatHilbertRandomStop
import HeatCompactTimeIntegrability
import SHE.LpIntegralFubini

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusScalarMode

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusMildProjection (project)
open SHE.StoppedItoInputs HeatTorusRealCoordinates
open HeatTorusFourier (frequencySquared frequencySquared_nonneg)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local notation "Finite" => HeatTorusGalerkinBackward.State
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (Finite S) :=
  InnerProductSpace.rclikeToReal ℂ (Finite S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (Finite S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (Finite S) := ⟨rfl⟩
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "Ω" => C(ℝ≥0, ℝ)
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable

variable {P : ℝ} {T : ℝ≥0} {M : RealState ι →L[ℝ] RealState ι}
  {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}

/-- The actual mild solution has a scalar damped equation for the real and
imaginary parts of each Fourier coefficient. -/
theorem equation (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g)
    (Y : ℝ≥0 → Ω → RealState ι) (hY : ∀ t, t ≤ T → Y t =ᵐ[μ] y.value t)
    (hYu : y.process =ᵐ[energyMeasure μ T] Function.uncurry Y)
    (n : Index ι) (t : ℝ≥0) (ht : t ≤ T) :
    let A := coordinate n
    let J := HeatCanonicalNative.scalar T
    let u := HeatPredictableObservation.lift F μ T M y.process
    let q := HeatHilbertRandomStop.project F μ T A u
    ∀ᵐ ω ∂μ, A (Y t ω) + frequencySquared P n.1 * (∫ r, A (Y r ω) ∂timeMeasure t) =
      A g + (∫ r, A (f (r,ω)) ∂timeMeasure t) + J.integral (stop F μ T t q) ω := by
  dsimp only
  classical
  let S : Finset (ι → ℤ) := {n.1}
  let k : ↥S := ⟨n.1, Finset.mem_singleton_self _⟩
  let L := HeatTorusGalerkinBackward.laplace S P
  let A := project S
  let C := coordinate n
  let Q := (component n.2).comp ((EuclideanSpace.proj k).restrictScalars ℝ)
  let c := frequencySquared P n.1
  let J := HeatCanonicalNative.scalar T
  let I := HeatTorusCanonicalIto.integral ι T
  let u := HeatPredictableObservation.lift F μ T M y.process
  let q := HeatHilbertRandomStop.project F μ T C u
  have hQA : Q.comp A = C := by
    ext x
    change component n.2 (HeatTorusGalerkinProjection.analysis S (embed x) k) =
      component n.2 (HeatTorusFourier.coefficientCLM n.1 (embed x))
    rw [HeatTorusGalerkinProjection.analysis_apply, HeatTorusFourier.coefficientCLM_apply] <;> rfl
  have hQL : Q.comp L = (-c) • Q := by
    apply ContinuousLinearMap.ext
    intro x
    change component n.2 (L x k) = (-c) • component n.2 (x k)
    rw [HeatTorusGalerkinBackward.laplace_apply]
    change component n.2 ((-c) • x k) = _
    exact (component n.2).map_smul _ _
  let K := C.compLpL 2 μ
  let B := Q.compLpL 2 μ
  let W (r : ℝ≥0) := K (y.value r)
  let Qf (r : ℝ≥0) := HeatTimeLpField.value μ (A ∘ f) r
  let Z := HeatStoppedPairing.value F μ T I u t
  have hK (x : Lp (RealState ι) 2 μ) : B ((A.compLpL 2 μ) x) = K x := by
    rw [HeatTerminalNaturality.compLp_comp, hQA]
  have hL (x : Lp (RealState ι) 2 μ) :
      B ((L.compLpL 2 μ) ((A.compLpL 2 μ) x)) = (-c) • K x := by
    let z := (A.compLpL 2 μ) x
    change B ((L.compLpL 2 μ) z) = _
    rw [← hK x, HeatTerminalNaturality.compLp_comp, hQL]
    apply Lp.ext
    filter_upwards [((-c) • Q).coeFn_compLpL z, Q.coeFn_compLpL z, Lp.coeFn_smul (-c) (B z)]
      with ω h₁ h₂ h₃
    change (((-c) • Q).compLpL 2 μ) z ω = ((-c) • B z) ω
    rw [h₁, h₃, Pi.smul_apply, show B z ω = Q (z ω) from h₂]
    rfl
  have hZ : (A.compLpL 2 μ) Z = HeatStoppedPairing.value F μ T (HeatTerminalNaturality.integral F μ T
      (HeatTorusGalerkinBackward.basis S) J) (HeatPredictableObservation.lift F μ T (A.comp M) y.process) t := by
    unfold Z HeatStoppedPairing.value I HeatTorusCanonicalIto.integral
    rw [HeatTerminalCrossNaturality.stopped_commutes F μ T (HeatTorusCanonicalIto.basis ι)
      (HeatTorusGalerkinBackward.basis S) J A t u]
    congr 2
    unfold u HeatPredictableObservation.lift
    letI : MeasurableSpace (ℝ≥0 × Ω) := (F).predictable
    exact HeatTerminalNaturality.compLp_comp _ A M y.process
  have hX (r : ℝ≥0) := (HeatTorusFourierWeak.of_mild hf hfi hfa y) S r
  let x (r : ℝ≥0) := ((L.compLpL 2 μ) ((A.compLpL 2 μ) (y.value r)))
  have hxi := HeatCompactTimeIntegrability.of_continuous x
    ((L.compLpL 2 μ).continuous.comp ((A.compLpL 2 μ).continuous.comp y.continuous_value)) t
  have hAf := (A.lipschitzWith.comp_memLp (map_zero A) hfi).mono_measure
    (Measure.prod_mono (HeatTimeRestriction.mono ht) le_rfl)
  have hqfi : Integrable Qf (timeMeasure t) :=
    (HeatTimeLpField.square_integrable μ (A ∘ f) (A.continuous.measurable.comp hf) t hAf).integrable one_le_two
  have hEq := congrArg B (hX t ht)
  change B ((A.compLpL 2 μ) (y.value t)) = B ((A.compLpL 2 μ) (Lp.const 2 μ g) +
    (∫ r, x r + Qf r ∂timeMeasure t) + _) at hEq
  rw [← hZ, integral_add hxi hqfi] at hEq
  simp only [map_add, hK] at hEq
  rw [← B.integral_comp_comm hxi, ← B.integral_comp_comm hqfi] at hEq
  have hdrift : (∫ r, B (x r) ∂timeMeasure t) = (-c) • (∫ r, W r ∂timeMeasure t) := by
    simp_rw [x, hL]
    exact integral_smul _ _
  rw [hdrift] at hEq
  let Dx : Lp ℝ 2 μ := ∫ r, W r ∂timeMeasure t
  let Fx : Lp ℝ 2 μ := ∫ r, B (Qf r) ∂timeMeasure t
  have hYint : Dx =ᵐ[μ] fun ω => ∫ r, C (Y r ω) ∂timeMeasure t := by
    have hu := (memLp_congr_ae hYu).mp (HeatPredictableObservation.ambient_memLp F μ T y.process)
    have hmem := hu.mono_measure (Measure.prod_mono (HeatTimeRestriction.mono ht) le_rfl)
    apply SHE.LpIntegralFubini.integral_ae μ (timeMeasure t) _
      (HeatCompactTimeIntegrability.of_continuous _ (K.continuous.comp y.continuous_value) t) _
      ((C.lipschitzWith.comp_memLp (map_zero C) hmem).integrable one_le_two)
    filter_upwards [timeMeasure_ae_mem t] with r hr
    filter_upwards [C.coeFn_compLpL (y.value r), hY r (hr.2.trans ht)] with ω h₁ h₂
    change (K (y.value r)) ω = C (Y r ω)
    rw [h₁, h₂]
  have hFint : Fx =ᵐ[μ] fun ω => ∫ r, C (f (r,ω)) ∂timeMeasure t := by
    have hf' := hfi.mono_measure (Measure.prod_mono (HeatTimeRestriction.mono ht) le_rfl)
    apply SHE.LpIntegralFubini.integral_ae μ (timeMeasure t) _ (B.integrable_comp hqfi) _
      ((C.lipschitzWith.comp_memLp (map_zero C) hf').integrable one_le_two)
    filter_upwards [HeatTimeLpField.value_ae μ (A ∘ f) (A.continuous.measurable.comp hf) t hAf] with r hr
    filter_upwards [Q.coeFn_compLpL (Qf r), hr] with ω h₁ h₂
    rw [h₁, h₂]
    exact congrArg (fun l : RealState ι →L[ℝ] ℝ => l (f (r,ω))) hQA
  have hz := HeatHilbertRandomStop.integral_projection F μ T (HeatTorusCanonicalIto.basis ι) J C (stop F μ T t u)
  rw [HeatHilbertRandomStop.project_stop] at hz
  change W t = K (Lp.const 2 μ g) + ((-c) • Dx + Fx) + K Z at hEq
  filter_upwards [hY t ht, C.coeFn_compLpL (y.value t), hYint, hFint,
    C.coeFn_compLpL (Lp.const 2 μ g), Lp.coeFn_const 2 μ g, C.coeFn_compLpL Z, hz,
    Lp.coeFn_add (K (Lp.const 2 μ g) + ((-c) • Dx + Fx)) (K Z),
    Lp.coeFn_add (K (Lp.const 2 μ g)) ((-c) • Dx + Fx), Lp.coeFn_add ((-c) • Dx) Fx,
    Lp.coeFn_smul (-c) Dx] with ω hy hw hd hf hkg hg hn hn' ha hb hfg hsmul
  change C (Z ω) = (J.integral (stop F μ T t q)) ω at hn'
  have he := congrArg (fun z : Lp ℝ 2 μ => z ω) hEq
  rw [ha, Pi.add_apply, hb, Pi.add_apply, hfg, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul,
    hw, ← hy, hkg, hg, hn, hn', hd, hf] at he
  simp only [Function.const_apply] at he
  change C (Y t ω) + c * (∫ r, C (Y r ω) ∂timeMeasure t) =
    C g + (∫ r, C (f (r,ω)) ∂timeMeasure t) + (J.integral (stop F μ T t q)) ω
  linarith only [he]

end HeatTorusScalarMode

#print axioms HeatTorusScalarMode.equation
