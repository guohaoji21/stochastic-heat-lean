import HeatDampedSlice
import HeatMildSolution

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace HeatConjugateSlices
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem representation (γ : ℝ) (g : E) (u : Process (E := E) F μ H) :
    ∀ᵐ t ∂timeMeasure H,
      (fun ω => PredictableExponential.conjugate F μ H γ
        (HeatVolterraForcing.orbit F μ H S hS hcontr g)
        (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I) u (t,ω)) =ᵐ[μ]
      (fun ω => Real.exp (-γ*(t:ℝ)) • S t g+
        I.integral (HeatDampedSlice.input F μ H S hS hcontr M γ t u) ω) := by
  let v := PredictableExponential.scale F μ H γ u
  let A := HeatVolterraForcing.orbit F μ H S hS hcontr g
  let V := HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I v
  have hs := Measure.ae_ae_of_ae_prod (PredictableExponential.ae F μ H (-γ) (A+V))
  have ha := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_add A V))
  have ho := Measure.ae_ae_of_ae_prod (HeatVolterraForcing.orbit_ae F μ H S hS hcontr g)
  have hv := HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem v
  filter_upwards [hs,ha,ho,hv,timeMeasure_ae_mem H] with t hs ha ho hv ht
  have hi : I.integral (HeatDampedSlice.input F μ H S hS hcontr M γ t u) =ᵐ[μ]
      (fun ω => Real.exp (-γ*(t:ℝ)) • I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t v) ω) := by
    unfold HeatDampedSlice.input
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [hs,ha,ho,hv,hi] with ω hs ha ho hv hi
  change PredictableExponential.scale F μ H (-γ) (A+V) (t,ω) = _
  rw [hs]
  simp only [PredictableExponential.weight,min_eq_left (show (t:ℝ)≤H from by exact_mod_cast ht.2),ha,
    Pi.add_apply,hi,smul_add]
  dsimp only [A,V,HeatVolterraFixedPoint.convolution]
  rw [ho,hv]

end HeatConjugateSlices
#check @HeatConjugateSlices.representation
#print axioms HeatConjugateSlices.representation
