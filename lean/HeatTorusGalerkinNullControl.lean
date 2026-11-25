import HeatTorusGalerkinControl
import HeatTorusProjectedForward

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section

namespace HeatTorusGalerkinNullControl

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns UnitAddTorus
open HeatTorusGalerkinBackward (State laplace multiplier)
open HeatTorusGalerkinProjection (analysis synthesis)
open HeatTorusControlObservation (Control inject)
open HeatTorusProjectedConvolution (fullHeat fullHeat_continuous fullHeat_contraction)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

local notation "Ω" => C(ℝ≥0, ℝ)
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : IsSeparable μ := HeatCanonicalSeparable.completed_separable
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

local notation "J" => fun H S => HeatTerminalNaturality.integral F μ H
  (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar H)

private theorem analysis_synthesis (S : Finset (ι → ℤ)) (x : State S) :
    analysis S (synthesis S x) = x := by
  ext k
  rw [HeatTorusGalerkinProjection.analysis_apply, HeatTorusGalerkinProjection.coefficient_synthesis,
    dite_eq_left k.property]

/-- Each predictable local input has an actual finite Galerkin trajectory
with the prescribed initial value, drift and diffusion. -/
theorem exists_trajectory (S : Finset (ι → ℤ)) (P : ℝ) (b : C(UnitAddTorus ι, ℂ))
    (O : Set (UnitAddTorus ι)) (H : ℝ≥0) (g : State S) (u : Process (E := Control O) F μ H) :
    ∃ X : HeatItoProductEnergy.Trajectory (J H S),
      Continuous X.state ∧ X.state 0 = Lp.const 2 μ g ∧
      (∀ t, AEStronglyMeasurable[F t] (X.state t : Ω → State S) μ) ∧
      (∀ᵐ t ∂timeMeasure H, X.drift t = ((laplace S P).compLpL 2 μ) (X.state t) +
        HeatBackwardEquationEnergy.slice (HeatPredictableObservation.lift F μ H (inject S O) u) t) ∧
      (∀ᵐ t ∂timeMeasure H, X.noise t = ((multiplier S b).compLpL 2 μ) (X.state t)) := by
  let A := (analysis S).restrictScalars ℝ
  let B := (synthesis S).restrictScalars ℝ
  let M := multiplier S b
  let G := B.comp (M.comp A)
  let U := HeatPredictableObservation.lift F μ H (inject S O) u
  let w := HeatPredictableObservation.lift F μ H B U
  let W := Function.curry (w : ℝ≥0 × Ω → Full)
  let f := HeatControlAdapted.clamp W H
  have hW : IsStronglyPredictable F W := Lp.stronglyMeasurable w
  have hWprog := hW.isStronglyProgressive
  have hWfi : Integrable (fun p : ℝ≥0 × Ω => ‖W p.1 p.2‖ ^ 2) (energyMeasure μ H) :=
    (HeatPredictableObservation.ambient_memLp F μ H w).norm.integrable_sq
  have hf := (HeatControlAdapted.clamp_measurable F W hWprog H).measurable
  have hfi := HeatClampedControl.square_integrable F μ H W hWprog hWfi
  have hfa := (HeatControlAdapted.clamp_progressive F W hWprog H).stronglyAdapted
  have hAB (x : State S) : A (B x) = x := analysis_synthesis S x
  obtain ⟨k, hk, ⟨β⟩⟩ := HeatCountableBasis.exists_countable_hilbertBasis (E := Full)
  let : Countable k := hk.to_subtype
  let x : Full := mFourierBasis (d := ι) (0 : ι → ℤ)
  have hx : ‖x‖ = 1 := (mFourierBasis (d := ι)).orthonormal.norm_eq_one _
  let : Nontrivial Full := ⟨⟨x, 0, fun he => by rw [he, norm_zero] at hx; exact zero_ne_one hx⟩⟩
  have hsem (s t : ℝ≥0) : fullHeat (ι := ι) P (s + t) = (fullHeat P s).comp (fullHeat P t) := by
    apply ContinuousLinearMap.ext
    intro y
    exact congrArg (fun (op : Full →L[ℂ] Full) => op y)
      (HeatTorusFourier.heat_add (ι := ι) P s.property t.property)
  have hzero : fullHeat (ι := ι) P 0 = ContinuousLinearMap.id ℝ Full := by
    apply ContinuousLinearMap.ext
    intro y
    change HeatTorusFourier.heat P 0 y = y
    rw [HeatTorusFourier.heat_zero]
    rfl
  let I := HeatTerminalNaturality.integral F μ H β (HeatCanonicalNative.scalar H)
  obtain ⟨_, v, V, _, hVc, hV0, hVa, hVu, hVr⟩ :=
    HeatControlledMild.exists_solution F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P)
      G hsem I hzero HeatCanonicalNullComplete.contains_nulls W hWprog hWfi (B g)
  obtain ⟨X, hX, hD, hN⟩ := HeatTorusProjectedForward.exists_projected_trajectory F μ H S P G β
    (HeatTorusGalerkinBackward.basis S) (HeatCanonicalNative.scalar H) f hf hfi hfa
    (B g) v V hVc hV0 hVa hVu hVr
  have hX0 : X.state 0 = Lp.const 2 μ g := by
    rw [hX 0, hV0]
    apply Lp.ext
    filter_upwards [A.coeFn_compLpL (Lp.const 2 μ (B g)), Lp.coeFn_const 2 μ (B g), Lp.coeFn_const 2 μ g]
      with ω hA hB hg
    rw [hA, hB, hg]
    exact hAB g
  refine ⟨X, ?_, hX0, ?_, ?_, ?_⟩
  · rw [show X.state = (fun t => (A.compLpL 2 μ) (V t)) from funext hX]
    exact (A.compLpL 2 μ).continuous.comp hVc
  · intro t
    rw [hX t]
    obtain ⟨Y, hYm, hY⟩ := hVa t
    exact (A.continuous.comp_stronglyMeasurable hYm).aestronglyMeasurable.congr
      ((A.coeFn_compLpL (V t)).trans (hY.fun_comp A)).symm
  · have hfU : (A ∘ f) =ᵐ[energyMeasure μ H] (U : ℝ≥0 × Ω → State S) := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H),
        HeatPredictableObservation.lift_ae F μ H B U] with p hp hw
      change A (w (min p.1 H, p.2)) = U p
      rw [min_eq_left hp.2, hw]
      exact hAB _
    have hfmeas := A.continuous.measurable.comp hf
    have hfmem := A.lipschitzWith.comp_memLp (map_zero A) hfi
    filter_upwards [HeatTimeLpField.value_ae μ (A ∘ f) hfmeas H hfmem,
      Measure.ae_ae_of_ae_prod hfU, HeatPredictableObservation.slice_ae F μ H U] with t ht hu hs
    rw [hD t]
    congr 1
    apply Lp.ext
    have he : (fun ω => A (f (t, ω))) =ᵐ[μ] fun ω => U (t, ω) := hu
    exact ht.trans (he.trans hs)
  · have hG : A.comp G = M.comp A := by
      apply ContinuousLinearMap.ext
      intro y
      exact hAB (M (A y))
    filter_upwards [hN] with t ht
    rw [ht, hX t, hG, HeatTerminalNaturality.compLp_comp]

/-- A uniformly bounded local control drives the actual finite Galerkin
equation to zero at the specified horizon. -/
theorem exists_null_control {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ)) (hb : ∀ x, (b x).im = 0)
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * HeatGevreyFourierExtension.weight k))
    {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty) {H : ℝ≥0} (hH : 0 < H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset (ι → ℤ)) (g : State S),
      ∃ (u : Process (E := Control O) F μ H) (X : HeatItoProductEnergy.Trajectory (J H S)),
        ‖u‖ ≤ K * ‖g‖ ∧ Continuous X.state ∧ X.state 0 = Lp.const 2 μ g ∧
        (∀ t, AEStronglyMeasurable[F t] (X.state t : Ω → State S) μ) ∧
        (∀ᵐ t ∂timeMeasure H, X.drift t = ((laplace S P).compLpL 2 μ) (X.state t) +
          HeatBackwardEquationEnergy.slice (HeatPredictableObservation.lift F μ H (inject S O) u) t) ∧
        (∀ᵐ t ∂timeMeasure H, X.noise t = ((multiplier S b).compLpL 2 μ) (X.state t)) ∧
        X.state H = 0 := by
  obtain ⟨K, hK, hc⟩ := HeatTorusGalerkinControl.exists_null_control hP hC ha b hb hdec hO hOne hH
  refine ⟨K, hK, fun S g => ?_⟩
  obtain ⟨u, hu, he⟩ := hc S (Lp.const 2 μ g)
  obtain ⟨X, hXc, hX0, hXa, hD, hN⟩ := exists_trajectory S P b O H g u
  have hg : ‖Lp.const 2 μ g‖ = ‖g‖ := by
    rw [Lp.norm_const _ _ _ (by norm_num), Measure.real, measure_univ, ENNReal.toReal_one,
      Real.one_rpow, mul_one]
  rw [hg] at hu
  exact ⟨u, X, hu, hXc, hX0, hXa, hD, hN, he X hX0 (hXa H) hD hN⟩

end HeatTorusGalerkinNullControl

#print axioms HeatTorusGalerkinNullControl.exists_trajectory
#print axioms HeatTorusGalerkinNullControl.exists_null_control
