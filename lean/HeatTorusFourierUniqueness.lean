import HeatProjectedUniqueness
import HeatTorusFourierWeak
import HeatTorusFrequencyExhaustion
import HeatZeroGronwall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatTorusFourierUniqueness

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusMildProjection (project)
open SHE.StoppedItoInputs
open scoped NNReal ENNReal Topology

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

theorem embed_norm (x : RealState ι) : ‖embed x‖ = ‖x‖ := by
  have h₁ := Complex.ofRealCLM.norm_compLp_le x
  rw [Complex.ofRealCLM_norm, one_mul] at h₁
  have h₂ := Complex.reCLM.norm_compLp_le (embed x)
  change ‖realPart (embed x)‖ ≤ ‖Complex.reCLM‖ * ‖embed x‖ at h₂
  rw [realPart_embed, Complex.reCLM_norm, one_mul] at h₂
  exact le_antisymm h₁ h₂

private theorem project_norm (S : Finset (ι → ℤ)) (x : RealState ι) : ‖project S x‖ ≤ ‖x‖ :=
  (HeatTorusGalerkinProjection.analysis_contraction S (embed x)).trans_eq (embed_norm x)

private theorem projectLp_norm (S : Finset (ι → ℤ)) (x : Lp (RealState ι) 2 μ) :
    ‖((project S).compLpL 2 μ) x‖ ≤ ‖x‖ := by
  have h : ‖((project S).compLpL 2 μ) x‖ ≤ 1 * ‖x‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(project S).coeFn_compLpL x] with ω hω
    rw [hω, one_mul]
    exact project_norm S (x ω)
  simpa only [one_mul] using h

private theorem projectLp_sq_tendsto (x : Lp (RealState ι) 2 μ) :
    Tendsto (fun n => ‖((project (HeatTorusFrequencyExhaustion.box ι n)).compLpL 2 μ) x‖ ^ 2)
      atTop (𝓝 (‖x‖ ^ 2)) := by
  let e : RealState ι →L[ℝ] Full := embed
  let z := (e.compLpL 2 μ) x
  have hz : ‖z‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [realLp_norm_sq, realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [e.coeFn_compLpL x] with ω hω
    change z ω = e (x ω) at hω
    rw [hω, embed_norm]
  have h := (HeatTorusFrequencyExhaustion.box_projectLp_tendsto z).norm.pow 2
  rw [hz] at h
  convert h using 1
  funext n
  let S := HeatTorusFrequencyExhaustion.box ι n
  let Q := HeatTorusGalerkinProjection.project S
  let A := HeatTorusMildProjection.project S
  rw [realLp_norm_sq, realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLpL x, Q.coeFn_compLpL z, e.coeFn_compLpL x] with ω hA hQ he
  change ‖((A.compLpL 2 μ) x) ω‖ ^ 2 = ‖((Q.compLpL 2 μ) z) ω‖ ^ 2
  rw [hA, hQ, show z ω = e (x ω) from he]
  change ‖HeatTorusGalerkinProjection.analysis S (e (x ω))‖ ^ 2 =
    ‖HeatTorusGalerkinProjection.synthesis S (HeatTorusGalerkinProjection.analysis S (e (x ω)))‖ ^ 2
  rw [HeatTorusGalerkinProjection.synthesis_norm]

variable {P : ℝ} {T : ℝ≥0} {M : RealState ι →L[ℝ] RealState ι}
  {f : ℝ≥0 × Ω → RealState ι} {g : RealState ι}

/-- The Fourier weak identity determines the same time values as the mild
solution, in particular the terminal random variable. -/
theorem value_eq_mild (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ T))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (y : HeatTorusGevreyObstruction.MildSolution P T M f g)
    (u : Process (E := RealState ι) F μ T) (V : ℝ≥0 → Lp (RealState ι) 2 μ)
    (hc : Continuous V) (h0 : V 0 = Lp.const 2 μ g)
    (ha : ∀ r, AEStronglyMeasurable[F r] (V r : Ω → RealState ι) μ)
    (hu : ∀ᵐ r ∂timeMeasure T, (fun ω => u (r, ω)) =ᵐ[μ] V r)
    (hw : HeatTorusFourierWeak.Holds (P := P) (M := M) (f := f) (g := g) u V) :
    ∀ t, t ≤ T → V t = y.value t := by
  let d (r : ℝ≥0) := V r - y.value r
  have hd : Continuous d := hc.sub y.continuous_value
  have hdc {t : ℝ≥0} : MemLp d 2 (timeMeasure t) := by
    obtain ⟨K, hK, h⟩ := HeatCompactLpBound.exists_bound μ t d hd
    apply (memLp_const K).mono' hd.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem t] with r hr
    simpa only [Real.norm_eq_abs, abs_of_nonneg hK] using h _ hr.2
  have hL (t : ℝ≥0) (ht : t ≤ T) (S : Finset (ι → ℤ)) :
      ‖((project S).compLpL 2 μ) (d t)‖ ^ 2 ≤
        ‖M‖ ^ 2 * ∫ r, ‖d r‖ ^ 2 ∂timeMeasure t := by
    obtain ⟨X, hX, hXd, hXn⟩ := HeatTorusFourierWeak.trajectory hf hfi hfa u V hc h0 ha hu hw S
    obtain ⟨Y, hY, hYd, hYn⟩ := HeatTorusFourierWeak.trajectory hf hfi hfa y.process y.value
      y.continuous_value y.initial_value y.adapted_value y.slices (HeatTorusFourierWeak.of_mild hf hfi hfa y) S
    have hz : X.state 0 = Y.state 0 := by rw [hX, hY, h0, y.initial_value]
    have hE := HeatProjectedUniqueness.difference_bound
      (HeatTerminalNaturality.locality F μ T _ _ (HeatCanonicalNative.locality T))
      X Y hz _ hXd hYd t ht
    rw [hX, hY, ← map_sub] at hE
    apply hE.trans
    rw [← integral_const_mul]
    apply integral_mono
    · exact ((X.noise_square.sub Y.noise_square).mono_measure (HeatTimeRestriction.mono ht)).norm.integrable_sq
    · exact hdc.norm.integrable_sq.const_mul _
    · intro r
      change ‖X.noise r - Y.noise r‖ ^ 2 ≤ ‖M‖ ^ 2 * ‖d r‖ ^ 2
      rw [hXn, hYn, ← map_sub, ← HeatTerminalNaturality.compLp_comp μ (project S) M]
      change ‖((project S).compLpL 2 μ) ((M.compLpL 2 μ) (d r))‖ ^ 2 ≤ _
      rw [← mul_pow]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      exact (projectLp_norm S _).trans (((M.compLpL 2 μ).le_opNorm (d r)).trans
        (mul_le_mul_of_nonneg_right (M.norm_compLpL_le) (norm_nonneg _)))
  have hB (t : ℝ≥0) (ht : t ≤ T) : ‖d t‖ ^ 2 ≤ ‖M‖ ^ 2 * ∫ r, ‖d r‖ ^ 2 ∂timeMeasure t :=
    le_of_tendsto (projectLp_sq_tendsto (d t))
      (Eventually.of_forall fun n => hL t ht (HeatTorusFrequencyExhaustion.box ι n))
  intro t ht
  have h0 := HeatZeroGronwall.zero T (fun r => ‖d r‖ ^ 2) (hd.norm.pow 2)
    (fun _ => sq_nonneg _) (‖M‖ ^ 2) (sq_nonneg _) hB t ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h0))

end HeatTorusFourierUniqueness

#print axioms HeatTorusFourierUniqueness.value_eq_mild
