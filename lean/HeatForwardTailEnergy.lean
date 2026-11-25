import HeatDecayingConvolutionEnergy
import HeatVolterraUniformEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3300000
noncomputable section

namespace HeatForwardTailEnergy

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω E κ : Type*} [mΩ : MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def energyBound (H : ℝ≥0) (M : E →L[ℝ] E) (g : E) (e : ℝ) : ℝ :=
  ‖g‖ ^ 2 + (H : ℝ) * e + ‖M‖ ^ 2 *
    (2 * (HeatVolterraUniformEnergy.stabilityConstant H M) ^ 2 *
      ((H : ℝ) * ‖g‖ ^ 2 + (H : ℝ) ^ 2 * e))

def controlEnergy (H : ℝ≥0) (f : ℝ≥0 × Ω → E) : ℝ :=
  ∫ p : ℝ≥0 × Ω, ‖f p‖ ^ 2 ∂energyMeasure μ H

def trajectoryEnergy (H : ℝ≥0) (Q : E →L[ℝ] E) (V : ℝ≥0 → Lp E 2 μ) : ℝ :=
  ∫ t : ℝ≥0, ‖(Q.compLpL 2 μ) (V t)‖ ^ 2 ∂timeMeasure H

local notation "ν" => Measure.trim (energyMeasure μ H) (predictable_le_product F)

def projectProcess (Q : E →L[ℝ] E) (v : Process (E := E) F μ H) :
    Process (E := E) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (Q.compLpL 2 ν) v

omit [IsProbabilityMeasure μ] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem projectProcess_ae (Q : E →L[ℝ] E) (v : Process (E := E) F μ H) :
    (projectProcess F μ H Q v : ℝ≥0 × Ω → E) =ᵐ[energyMeasure μ H] fun p => Q (v p) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ae_eq_of_ae_eq_trim (Q.coeFn_compLpL v)

omit [IsProbabilityMeasure μ] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
private theorem project_add (Q : E →L[ℝ] E) (u v : Process (E := E) F μ H) :
    projectProcess F μ H Q (u + v) = projectProcess F μ H Q u + projectProcess F μ H Q v := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (Q.compLpL 2 ν).map_add u v

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
private theorem project_energy (Q : E →L[ℝ] E) (v : Process (E := E) F μ H)
    (V : ℝ≥0 → Lp E 2 μ)
    (hv : ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] V t) :
    ‖projectProcess F μ H Q v‖ ^ 2 = ∫ t, ‖(Q.compLpL 2 μ) (V t)‖ ^ 2 ∂timeMeasure H := by
  rw [process_integral_energy]
  apply integral_congr_ae
  filter_upwards [hv, Measure.ae_ae_of_ae_prod (projectProcess_ae F μ H Q v)] with t hv hQ
  rw [realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [hv, hQ, Q.coeFn_compLpL (V t)] with ω hv hQ hV
  rw [hQ, hv, hV]

variable (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M Q : E →L[ℝ] E)
  (hsem : ∀ s t, S (s + t) = (S s).comp (S t))
  (b : HilbertBasis κ ℝ E) (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)

local notation "I" => HeatTerminalNaturality.integral F μ H b J
local notation "N" => HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I
local notation "O" => HeatVolterraForcing.orbit F μ H S hS hcontr

/-- An integrated estimate for the spatial image of the actual fixed point,
uniform in all inputs of bounded square-integrable energy. -/
theorem bound {γ : ℝ} (hγ : 0 < γ)
    (hdecay : ∀ t x, ‖Q (S t x)‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖x‖)
    (g : E) (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ H))
    (a u : Process (E := E) F μ H) (hfix : u = O g + a + N u)
    (ha : ∀ᵐ t ∂timeMeasure H, (fun ω => a (t, ω)) =ᵐ[μ] HeatControlConvolution.value H S f t)
    (V : ℝ≥0 → Lp E 2 μ) (hV : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] V t) :
    trajectoryEnergy μ H Q V ≤
      3 * HeatRegularKernel.mass γ * energyBound H M g (controlEnergy μ H f) := by
  let forceEnergy := controlEnergy μ H f
  let C := HeatVolterraUniformEnergy.stabilityConstant H M
  let proj := projectProcess F μ H Q
  let L := HeatRegularKernel.mass γ
  have hL : 0 ≤ L := HeatRegularKernel.mass_nonneg _ hγ
  have hE : 0 ≤ forceEnergy := integral_nonneg fun _ => sq_nonneg _
  have hproj (v : Process (E := E) F μ H) (x : ℝ≥0 → Ω → E)
      (hx : ∀ᵐ t ∂timeMeasure H, (fun ω => v (t, ω)) =ᵐ[μ] x t) :
      ENNReal.ofReal (‖proj v‖ ^ 2) =
        ∫⁻ t, ∫⁻ ω, ENNReal.ofReal (‖Q (x t ω)‖ ^ 2) ∂μ ∂timeMeasure H := by
    rw [process_lintegral_energy]
    apply lintegral_congr_ae
    filter_upwards [hx, Measure.ae_ae_of_ae_prod (projectProcess_ae F μ H Q v)] with t hx hv
    apply lintegral_congr_ae
    filter_upwards [hx, hv] with ω hx hv
    rw [hv, hx]
  have hg : ‖proj (O g)‖ ^ 2 ≤ L * ‖g‖ ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL (sq_nonneg _))).mp
    rw [hproj (O g) (fun t _ => S t g)
      (Measure.ae_ae_of_ae_prod (HeatVolterraForcing.orbit_ae F μ H _ hS
        hcontr g)), ENNReal.ofReal_mul hL]
    simp only [lintegral_const, measure_univ, mul_one]
    exact HeatDecayingConvolutionEnergy.orbit H S Q hγ hdecay g
  have hinput : ENNReal.ofReal forceEnergy = ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖f (s, ω)‖ ^ 2) ∂μ ∂timeMeasure H := by
    change ENNReal.ofReal (∫ p : ℝ≥0 × Ω, ‖f p‖ ^ 2 ∂energyMeasure μ H) = _
    rw [ofReal_integral_eq_lintegral_ofReal hfi.norm.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)]
    exact lintegral_prod _ (ENNReal.continuous_ofReal.measurable.comp (hf.norm.pow_const 2)).aemeasurable
  have hfQ : ‖proj a‖ ^ 2 ≤ ((H : ℝ) * L) * forceEnergy := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg H.property hL) hE)).mp
    rw [hproj a (HeatControlConvolution.value H S f) ha,
      ENNReal.ofReal_mul (mul_nonneg H.property hL), hinput]
    exact HeatDecayingConvolutionEnergy.forcing μ H S Q hγ hdecay
      hS hcontr f hf hfi
  have hnoise : ‖proj (N u)‖ ^ 2 ≤ ‖M‖ ^ 2 * L * ‖u‖ ^ 2 := by
    rw [project_energy F μ H Q (N u) _ (HeatVolterraContinuity.convolution_slices F μ H
      S hS hcontr M I hsem u)]
    exact HeatDecayingConvolutionEnergy.stochastic μ H S Q M hγ hdecay
      F b J hS hcontr u
  have hu := HeatVolterraUniformEnergy.fixed_point_bound F μ H S
    hS hcontr M hsem I (O g + a) u hfix
  have ho := HeatVolterraUniformEnergy.orbit_energy F μ H S
    hS hcontr g
  have hfA : ‖a‖ ^ 2 ≤ (H : ℝ) ^ 2 * forceEnergy := HeatVolterraUniformEnergy.control_energy F μ H S
    hS hcontr f hf hfi a ha
  have hsum : ‖O g + a‖ ^ 2 ≤ 2 * ((H : ℝ) * ‖g‖ ^ 2 + (H : ℝ) ^ 2 * forceEnergy) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (O g) a) 2).trans ?_
    nlinarith [sq_nonneg (‖O g‖ - ‖a‖)]
  have hs : ‖u‖ ^ 2 ≤ 2 * C ^ 2 * ((H : ℝ) * ‖g‖ ^ 2 + (H : ℝ) ^ 2 * forceEnergy) := by
    change ‖u‖ ≤ C * ‖O g + a‖ at hu
    calc
      _ ≤ (C * ‖O g + a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      _ ≤ _ := by
        rw [mul_pow]
        exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg C)).trans_eq (by ring)
  have hp : proj u = proj (O g) + proj a + proj (N u) := by
    calc
      _ = proj (O g + a + N u) := congrArg proj hfix
      _ = proj (O g + a) + proj (N u) := project_add F μ H Q (O g + a) (N u)
      _ = _ := congrArg (fun z => z + proj (N u)) (project_add F μ H Q (O g) a)
  have hsumQ : ‖proj u‖ ^ 2 ≤
      3 * (‖proj (O g)‖ ^ 2 + ‖proj a‖ ^ 2 + ‖proj (N u)‖ ^ 2) := by
    have hn := (norm_add_le (proj (O g) + proj a) (proj (N u))).trans
      (add_le_add (norm_add_le (proj (O g)) (proj a)) le_rfl)
    rw [← hp] at hn
    refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ?_
    nlinarith [sq_nonneg (‖proj (O g)‖ - ‖proj a‖), sq_nonneg (‖proj (O g)‖ - ‖proj (N u)‖),
      sq_nonneg (‖proj a‖ - ‖proj (N u)‖)]
  unfold trajectoryEnergy
  rw [← project_energy F μ H Q u V hV]
  refine hsumQ.trans (le_trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hg hfQ) (hnoise.trans (mul_le_mul_of_nonneg_left hs
      (mul_nonneg (sq_nonneg _) hL)))) (by norm_num)) ?_)
  change 3 * (L * ‖g‖ ^ 2 + ((H : ℝ) * L) * forceEnergy + ‖M‖ ^ 2 * L *
    (2 * C ^ 2 * ((H : ℝ) * ‖g‖ ^ 2 + (H : ℝ) ^ 2 * forceEnergy))) ≤
      3 * L * (‖g‖ ^ 2 + (H : ℝ) * forceEnergy + ‖M‖ ^ 2 * (2 * C ^ 2 *
        ((H : ℝ) * ‖g‖ ^ 2 + (H : ℝ) ^ 2 * forceEnergy)))
  apply le_of_eq
  dsimp only [L]
  ring

end HeatForwardTailEnergy

#print axioms HeatForwardTailEnergy.bound
