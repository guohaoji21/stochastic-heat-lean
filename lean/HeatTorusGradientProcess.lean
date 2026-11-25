import HeatTorusSobolevForm
import HeatTorusGalerkinProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatTorusGradientProcess

open Filter MeasureTheory UnitAddTorus HeatTorusFourier HeatTorusGradient HeatTorusSobolevFourier
open scoped ENNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
local instance : MeasurableSpace (State ι) := borel _
local instance : BorelSpace (State ι) := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (State ι) := Lp.SecondCountableTopology

private theorem measurable_coefficient (u : Ω → State ι) (hu : Measurable u) (k : ι → ℤ) :
    Measurable (fun ω => mFourierCoeff (u ω) k) := by
  have he : (fun ω => mFourierCoeff (u ω) k) = (coefficientCLM k) ∘ u :=
    funext fun ω => (coefficientCLM_apply k (u ω)).symm
  rw [he]
  exact (coefficientCLM k).continuous.measurable.comp hu

private theorem measurable_modeEnergy (P : ℝ) (u : Ω → State ι) (hu : Measurable u) (k : ι → ℤ) :
    Measurable (fun ω => ENNReal.ofReal (modeEnergy P (u ω) k)) :=
  (measurable_const.mul ((measurable_coefficient u hu k).norm.pow_const 2)).ennreal_ofReal

/-- A uniform bound on finite Fourier energies gives integrable total energy.
The bound is taken over all finite sets of frequencies. -/
theorem lintegral_energy (P : ℝ) (ν : Measure Ω) (u : Ω → State ι) (hu : Measurable u)
    (B : ℝ≥0∞) (hB : ∀ S : Finset (ι → ℤ),
      (∫⁻ ω, ∑ k ∈ S, ENNReal.ofReal (modeEnergy P (u ω) k) ∂ν) ≤ B) :
    (∫⁻ ω, ∑' k : ι → ℤ, ENNReal.ofReal (modeEnergy P (u ω) k) ∂ν) ≤ B := by
  have hm := measurable_modeEnergy P u hu
  rw [lintegral_tsum (fun k => (hm k).aemeasurable), ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  rw [← lintegral_finsetSum S (fun k _ => hm k)]
  exact hB S

/-- Uniform integrated spectral energy bounds construct spatial derivatives
in the same measurable `L²` space as the process. The ambient measurable
space can be the predictable sigma algebra. -/
theorem exists_gradient (P : ℝ) (ν : Measure Ω) (u : Ω → State ι) (hu : Measurable u)
    (B : ℝ≥0∞) (hfinite : B < ∞)
    (hB : ∀ S : Finset (ι → ℤ), (∫⁻ ω, ∑ k ∈ S, ENNReal.ofReal (modeEnergy P (u ω) k) ∂ν) ≤ B) :
    ∃ D : ι → Ω → State ι, (∀ i, MemLp (D i) 2 ν) ∧
      ∀ᵐ ω ∂ν, HasGradient P (u ω) (fun i => D i ω) := by
  classical
  let q (ω : Ω) := ∑' k : ι → ℤ, ENNReal.ofReal (modeEnergy P (u ω) k)
  have hm : Measurable q := Measurable.tsum (measurable_modeEnergy P u hu)
  have hq : (∫⁻ ω, q ω ∂ν) < ∞ := (lintegral_energy P ν u hu B hB).trans_lt hfinite
  have hs : ∀ᵐ ω ∂ν, Summable (modeEnergy P (u ω)) := by
    filter_upwards [ae_lt_top hm hq.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (modeEnergy_nonneg P (u ω) _)] using ENNReal.summable_toReal hω.ne
  let D (i : ι) (ω : Ω) : State ι :=
    if h : Summable (modeEnergy P (u ω)) then (HeatTorusSobolevFourier.exists_gradient P (u ω) h).choose i else 0
  have hD : ∀ᵐ ω ∂ν, HasGradient P (u ω) (fun i => D i ω) := by
    filter_upwards [hs] with ω hω
    simpa only [D, dite_eq_left hω] using (HeatTorusSobolevFourier.exists_gradient P (u ω) hω).choose_spec
  have hDm (i : ι) : AEStronglyMeasurable (D i) ν := by
    let app (S : Finset (ι → ℤ)) (ω : Ω) : State ι := HeatTorusGalerkinProjection.synthesis S
      (WithLp.toLp 2 (fun k : ↥S => symbol P i k.val * mFourierCoeff (u ω) k.val))
    have happ (S : Finset (ι → ℤ)) : AEStronglyMeasurable (app S) ν := by
      have hpre : Measurable (fun ω => fun k : ↥S => symbol P i k.val * mFourierCoeff (u ω) k.val) := by
        apply Measurable.of_eval
        intro k
        exact measurable_const.mul (measurable_coefficient u hu k.val)
      exact ((HeatTorusGalerkinProjection.synthesis S).continuous.measurable.comp
        ((PiLp.continuous_toLp 2 (fun _ : ↥S => ℂ)).measurable.comp hpre)).stronglyMeasurable.aestronglyMeasurable
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (ι → ℤ))) happ
    filter_upwards [hD] with ω hω
    have he (S : Finset (ι → ℤ)) : app S ω = HeatTorusGalerkinProjection.project S (D i ω) := by
      change HeatTorusGalerkinProjection.synthesis S _ =
        HeatTorusGalerkinProjection.synthesis S (HeatTorusGalerkinProjection.analysis S (D i ω))
      congr 1
      ext k
      rw [HeatTorusGalerkinProjection.analysis_apply, hω i k.val]
    simpa only [he] using HeatTorusGalerkinProjection.project_tendsto (D i ω)
  refine ⟨D, fun i => ?_, hD⟩
  apply (memLp_two_iff_integrable_sq_norm (hDm i)).mpr
  refine ⟨(hDm i).norm.pow 2, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr ?_⟩
  have hle : (fun ω => ENNReal.ofReal (‖D i ω‖ ^ 2)) ≤ᵐ[ν] q := by
    filter_upwards [hD] with ω hω
    obtain ⟨hsum, henergy⟩ := gradient_energy P (u ω) (fun j => D j ω) hω
    have hone : ‖D i ω‖ ^ 2 ≤ ∑ j, ‖D j ω‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖D j ω‖) (Finset.mem_univ i)
    rw [henergy] at hone
    exact (ENNReal.ofReal_le_ofReal hone).trans_eq
      (ENNReal.ofReal_tsum_of_nonneg (modeEnergy_nonneg P (u ω)) hsum)
  exact (lintegral_mono_ae hle).trans_lt hq

end HeatTorusGradientProcess

#print axioms HeatTorusGradientProcess.lintegral_energy
#print axioms HeatTorusGradientProcess.exists_gradient
