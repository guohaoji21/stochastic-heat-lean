import HeatForcedMomentInvariant
import HeatMomentWeights
import HeatMomentUnweight

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatForcedMoment
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem exists_uniform (B : ℝ≥0) (hB : StandardTerminalBDGPower 8 I B)
    (A : Process (E := E) F μ H) (R : ℝ) (hR : 0≤R) (hA : A∈HeatMomentBall.Ball R) :
    ∃ u : Process (E := E) F μ H,
      u=A+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      ∃ K : ℝ, 0≤K ∧ u∈HeatMomentBall.Ball K := by
  obtain ⟨γ,hγ,hsmall,hsmallM⟩ := HeatMomentWeights.exists_weight (‖M‖^2) (B:ℝ)
  let N := HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I
  let Φ := PredictableExponential.conjugate F μ H γ A N
  let D : ℝ := (2:ℝ)^16*R
  have hD : 0≤D := mul_nonneg (by positivity) hR
  have hLip := HeatMomentWeights.lipschitz F μ H S hS hcontr M hsem I hγ hsmall A
  have hc : ContractingWith (1/2) Φ := ⟨by norm_num,hLip⟩
  have hmap : Set.MapsTo Φ (HeatMomentBall.Ball D) (HeatMomentBall.Ball D) :=
    HeatForcedMomentInvariant.maps_ball F μ H S hS hcontr M hsem I B hB hγ hR hD hsmallM A hA le_rfl
  let z := hc.fixedPoint Φ
  have hzmem : z∈HeatMomentBall.Ball D := by
    apply (HeatMomentBall.isClosed_ball (E:=E) (F:=F) (μ:=μ) (H:=H) D).mem_of_tendsto
      (hc.tendsto_iterate_fixedPoint (0 : Process (E := E) F μ H))
    exact Eventually.of_forall (fun n => (hmap.iterate n) (HeatMomentBall.zero_mem D))
  let u := PredictableExponential.scale F μ H γ z
  have hu : u=A+N u := by
    have hz : z=Φ z := hc.fixedPoint_isFixedPt.symm
    have he := congrArg (PredictableExponential.scale F μ H γ) hz
    simpa only [Φ,PredictableExponential.conjugate,PredictableExponential.cancel',u] using he
  have hweighted : PredictableExponential.scale F μ H (-γ) u∈HeatMomentBall.Ball D := by
    simpa only [u,PredictableExponential.cancel] using hzmem
  have huniform := HeatMomentUnweight.uniform F μ H γ hγ.le D (PredictableExponential.scale F μ H (-γ) u) hweighted
  rw [PredictableExponential.cancel'] at huniform
  exact ⟨u,hu,Real.exp (16*γ*(H:ℝ))*D,by positivity,huniform⟩

end HeatForcedMoment
#check @HeatForcedMoment.exists_uniform
#print HeatForcedMoment.exists_uniform
#print axioms HeatForcedMoment.exists_uniform
