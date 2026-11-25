import HeatTorusUniformTail
import HeatForwardTailEnergy
import HeatControlledMild
import HeatClampedControl
import HeatTorusGalerkinCompression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace HeatTorusUniformControlled

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusProjectedConvolution HeatTorusUniformTail HeatForwardTailEnergy
open scoped NNReal ENNReal Topology

variable {ι Ω κ : Type*} [Fintype ι] [mΩ : MeasurableSpace Ω] [Countable κ]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology

variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) {P : ℝ}

local notation "S" => fullHeat (ι := ι) P

/-- The solution constructed by the controlled mild equation has a Fourier
tail estimate uniform over all controls of bounded mean-square energy. -/
theorem exists_solution (hP : 0 < P)
    (b : C(UnitAddTorus ι, ℂ)) (β : HilbertBasis κ ℝ Full)
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (U : ℝ≥0 → Ω → Full) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ H)) (g : Full) :
    ∃ (u : Process (E := Full) F μ H) (V : ℝ≥0 → Lp Full 2 μ),
      Continuous V ∧ V 0 = Lp.const 2 μ g ∧
      (∀ t, ∃ Z : Ω → Full, StronglyMeasurable[F t] Z ∧ V t =ᵐ[μ] Z) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] V t) ∧
      (∀ t, V t =ᵐ[μ] fun ω => fullHeat P t g +
        HeatControlConvolution.value H (fullHeat P) (HeatControlAdapted.clamp U H) t ω +
        (HeatTerminalNaturality.integral (κ := κ) (E := Full) F μ H β J).integral
          (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P)
            (fullHeat_contraction P) (HeatTorusGalerkinCompression.fullMultiplier b) t u) ω) ∧
      ∀ n, trajectoryEnergy μ H (tail (ι := ι) n) V ≤
        3 * HeatRegularKernel.mass (rate P n) *
          energyBound H (HeatTorusGalerkinCompression.fullMultiplier b) g
            (controlEnergy μ H (Function.uncurry U)) := by
  let I := HeatTerminalNaturality.integral (κ := κ) (E := Full) F μ H β J
  let M := HeatTorusGalerkinCompression.fullMultiplier b
  have hsem (s t : ℝ≥0) : S (s + t) = (S s).comp (S t) := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun (op : Full →L[ℂ] Full) => op x)
      (HeatTorusFourier.heat_add (ι := ι) P s.property t.property)
  have hzero : S 0 = ContinuousLinearMap.id ℝ Full := by
    apply ContinuousLinearMap.ext
    intro x
    change HeatTorusFourier.heat P 0 x = x
    rw [HeatTorusFourier.heat_zero]
    rfl
  let x : Full := mFourierBasis (d := ι) (0 : ι → ℤ)
  have hx : ‖x‖ = 1 := (mFourierBasis (d := ι)).orthonormal.norm_eq_one _
  let : Nontrivial Full := ⟨⟨x, 0, fun he => by rw [he, norm_zero] at hx; exact zero_ne_one hx⟩⟩
  obtain ⟨a, u, V, hfix, hVc, hV0, hVa, hVu, hVr⟩ :=
    HeatControlledMild.exists_solution F μ H S (fullHeat_continuous P) (fullHeat_contraction P)
      M hsem I hzero hn U hU hE g
  let f := HeatControlAdapted.clamp U H
  have hfm : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfi : MemLp f 2 (energyMeasure μ H) := HeatClampedControl.square_integrable F μ H U hU hE
  have hfE : controlEnergy μ H f = controlEnergy μ H (Function.uncurry U) := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    change ‖U (min p.1 H) p.2‖ ^ 2 = ‖U p.1 p.2‖ ^ 2
    rw [min_eq_left hp.2]
  let o := HeatVolterraForcing.orbit F μ H S (fullHeat_continuous P) (fullHeat_contraction P) g
  let v := HeatVolterraFixedPoint.convolution F μ H S (fullHeat_continuous P)
    (fullHeat_contraction P) M hsem I u
  have hsum : ∀ᵐ p ∂energyMeasure μ H, u p = o p + a p + v p := by
    have h1 := ae_eq_of_ae_eq_trim (Lp.coeFn_add (o + a) v)
    have h2 := ae_eq_of_ae_eq_trim (Lp.coeFn_add o a)
    change u = o + a + v at hfix
    rw [← hfix] at h1
    filter_upwards [h1, h2] with p h1 h2
    exact h1.trans (congrArg (fun z : Full => z + v p) h2)
  have ha : ∀ᵐ t ∂timeMeasure H, (fun ω => a (t, ω)) =ᵐ[μ] HeatControlConvolution.value H S f t := by
    filter_upwards [Measure.ae_ae_of_ae_prod hsum, hVu,
      Measure.ae_ae_of_ae_prod (HeatVolterraForcing.orbit_ae F μ H S
        (fullHeat_continuous P) (fullHeat_contraction P) g),
      HeatVolterraContinuity.convolution_slices F μ H S
        (fullHeat_continuous P) (fullHeat_contraction P) M I hsem u] with t hsum hu ho hv
    filter_upwards [hsum, hu, ho, hv, hVr t] with ω hsum hu ho hv hV
    have h := hsum.symm.trans (hu.trans hV)
    change o (t, ω) = S t g at ho
    change v (t, ω) = _ at hv
    rw [ho, hv] at h
    exact add_left_cancel (add_right_cancel h)
  refine ⟨u, V, hVc, hV0, hVa, hVu, hVr, fun n => ?_⟩
  have ht := HeatForwardTailEnergy.bound (E := Full) (κ := κ) F μ H S (fullHeat_continuous P)
    (fullHeat_contraction P) M (tail (ι := ι) n) hsem β J (rate_pos hP n) (heat_decay P n)
    g f hfm hfi a u hfix ha V hVu
  rw [hfE] at ht
  exact ht

end HeatTorusUniformControlled

#print axioms HeatTorusUniformControlled.exists_solution
