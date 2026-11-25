import HeatStoppedPairing
import HeatBoundedPairing

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatItoProduct
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem product_rule (hl : StandardTerminalPastLocality I)
    (x₀ z₀ : Lp E 2 μ) (hx₀ : AEStronglyMeasurable[F 0] x₀ μ)
    (hz₀ : AEStronglyMeasurable[F 0] z₀ μ)
    (f g : ℝ≥0 → Lp E 2 μ) (hf : Integrable f (timeMeasure H)) (hg : Integrable g (timeMeasure H))
    (ha : ∀ᵐ t ∂timeMeasure H, AEStronglyMeasurable[F t] (f t) μ)
    (hb : ∀ᵐ t ∂timeMeasure H, AEStronglyMeasurable[F t] (g t) μ)
    (h k : Process (E := E) F μ H) :
    let X := fun t => x₀+HeatDeterministicPairing.cumulative (timeMeasure H) f t+HeatStoppedPairing.value F μ H I h t
    let Z := fun t => z₀+HeatDeterministicPairing.cumulative (timeMeasure H) g t+HeatStoppedPairing.value F μ H I k t
    inner ℝ (x₀+(∫ t,f t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I h H)
      (z₀+(∫ t,g t ∂timeMeasure H)+HeatStoppedPairing.value F μ H I k H)-inner ℝ x₀ z₀=
      (∫ t,inner ℝ (f t) (Z t) ∂timeMeasure H)+
      (∫ t,inner ℝ (X t) (g t) ∂timeMeasure H)+
      inner ℝ (StoppedItoInputs.stop F μ H H h) (StoppedItoInputs.stop F μ H H k) := by
  let ν := timeMeasure H
  let A := HeatDeterministicPairing.cumulative ν f
  let B := HeatDeterministicPairing.cumulative ν g
  let M := HeatStoppedPairing.value F μ H I h
  let N := HeatStoppedPairing.value F μ H I k
  have hAi := HeatDeterministicPairing.cumulative_integrable ν f hf
  have hBi := HeatDeterministicPairing.cumulative_integrable ν g hg
  have hMi := HeatStoppedPairing.value_integrable F μ H I h
  have hNi := HeatStoppedPairing.value_integrable F μ H I k
  have hMB (t : ℝ≥0) : ‖M t‖≤‖h‖ := by
    change ‖I.integral (StoppedItoInputs.stop F μ H t h)‖≤‖h‖
    rw [I.integral.norm_map]
    exact StoppedInputResolvent.stop_norm_le F μ H h t
  have hNB (t : ℝ≥0) : ‖N t‖≤‖k‖ := by
    change ‖I.integral (StoppedItoInputs.stop F μ H t k)‖≤‖k‖
    rw [I.integral.norm_map]
    exact StoppedInputResolvent.stop_norm_le F μ H k t
  have hfB : Integrable (fun t => inner ℝ (f t) (B t)) ν :=
    HeatBoundedPairing.integrable ν f B hf hBi.aestronglyMeasurable _
      (Eventually.of_forall (HeatIntegralBounds.cumulative_bound ν g hg))
  have hgA : Integrable (fun t => inner ℝ (g t) (A t)) ν :=
    HeatBoundedPairing.integrable ν g A hg hAi.aestronglyMeasurable _
      (Eventually.of_forall (HeatIntegralBounds.cumulative_bound ν f hf))
  have hfN : Integrable (fun t => inner ℝ (f t) (N t)) ν :=
    HeatBoundedPairing.integrable ν f N hf hNi.aestronglyMeasurable ‖k‖ (Eventually.of_forall hNB)
  have hgM : Integrable (fun t => inner ℝ (g t) (M t)) ν :=
    HeatBoundedPairing.integrable ν g M hg hMi.aestronglyMeasurable ‖h‖ (Eventually.of_forall hMB)
  have hAg : Integrable (fun t => inner ℝ (A t) (g t)) ν := by
    simpa only [real_inner_comm] using hgA
  have hMg : Integrable (fun t => inner ℝ (M t) (g t)) ν := by
    simpa only [real_inner_comm] using hgM
  have hleft : (∫ t,inner ℝ (f t) (z₀+B t+N t) ∂ν)=
      inner ℝ (∫ t,f t ∂ν) z₀+(∫ t,inner ℝ (f t) (B t) ∂ν)+
        inner ℝ (∫ t,f t ∂ν) (N H) := by
    simp_rw [inner_add_right]
    rw [integral_add (f := fun t => inner ℝ (f t) z₀+inner ℝ (f t) (B t))
      (g := fun t => inner ℝ (f t) (N t)) ((hf.inner_const z₀).add hfB) hfN,
      integral_add (f := fun t => inner ℝ (f t) z₀) (g := fun t => inner ℝ (f t) (B t)) (hf.inner_const z₀) hfB]
    have hc : (∫ t,inner ℝ (f t) z₀ ∂ν)=inner ℝ (∫ t,f t ∂ν) z₀ := by
      calc
        _ = ∫ t,inner ℝ z₀ (f t) ∂ν := integral_congr_ae (Eventually.of_forall (fun t => real_inner_comm _ _))
        _ = inner ℝ z₀ (∫ t,f t ∂ν) := integral_inner hf _
        _ = _ := real_inner_comm _ _
    rw [hc,← HeatStoppedPairing.drift_pairing F μ H I hl k f hf ha]
  have hright : (∫ t,inner ℝ (x₀+A t+M t) (g t) ∂ν)=
      inner ℝ x₀ (∫ t,g t ∂ν)+(∫ t,inner ℝ (A t) (g t) ∂ν)+
        inner ℝ (M H) (∫ t,g t ∂ν) := by
    simp_rw [inner_add_left]
    rw [integral_add (f := fun t => inner ℝ x₀ (g t)+inner ℝ (A t) (g t))
      (g := fun t => inner ℝ (M t) (g t)) ((hg.const_inner x₀).add hAg) hMg,
      integral_add (f := fun t => inner ℝ x₀ (g t)) (g := fun t => inner ℝ (A t) (g t)) (hg.const_inner x₀) hAg,
      integral_inner hg]
    have hp := HeatStoppedPairing.drift_pairing F μ H I hl h g hg hb
    have hc : (∫ t,inner ℝ (M t) (g t) ∂ν)=inner ℝ (M H) (∫ t,g t ∂ν) := by
      calc
        _ = ∫ t,inner ℝ (g t) (M t) ∂ν := integral_congr_ae (Eventually.of_forall (fun t => real_inner_comm _ _))
        _ = inner ℝ (∫ t,g t ∂ν) (M H) := hp.symm
        _ = _ := real_inner_comm _ _
    rw [hc]
  have hzeroX : inner ℝ x₀ (N H)=0 := by
    have hp := HeatStoppedPairing.past_pairing F μ H I hl k (t := 0) (by positivity) x₀ hx₀
    simpa only [M,N,HeatStoppedPairing.value,NNReal.coe_zero,StoppedItoInputs.stop_zero,map_zero,inner_zero_right] using hp
  have hzeroZ : inner ℝ (M H) z₀=0 := by
    have hp := HeatStoppedPairing.past_pairing F μ H I hl h (t := 0) (by positivity) z₀ hz₀
    have hz : inner ℝ z₀ (M H)=0 := by
      simpa only [M,N,HeatStoppedPairing.value,NNReal.coe_zero,StoppedItoInputs.stop_zero,map_zero,inner_zero_right] using hp
    exact (real_inner_comm _ _).trans hz
  have hcross : inner ℝ (M H) (N H)=inner ℝ (StoppedItoInputs.stop F μ H H h) (StoppedItoInputs.stop F μ H H k) :=
    I.integral.inner_map_map _ _
  have hdet := HeatDeterministicPairing.product_rule ν f g hf hg
  change inner ℝ (x₀+(∫ t,f t ∂ν)+M H) (z₀+(∫ t,g t ∂ν)+N H)-inner ℝ x₀ z₀=
    (∫ t,inner ℝ (f t) (z₀+B t+N t) ∂ν)+(∫ t,inner ℝ (x₀+A t+M t) (g t) ∂ν)+_
  rw [hleft,hright]
  simp only [inner_add_left,inner_add_right]
  linarith

end HeatItoProduct
#check @HeatItoProduct.product_rule
#print HeatItoProduct.product_rule
#print axioms HeatItoProduct.product_rule
