import HeatConvolutionStopLocality
import HeatConvolutionAlgebra
import HeatMomentWeights

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatLocalUniqueness
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem unique_before (hlocal : StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (hs : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0)<τ p.2})
    (A B u v : Process (E := E) F μ H)
    (hu : u=A+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I) u)
    (hv : v=B+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I) v)
    (hAB : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 → A p=B p) :
    ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 → u p=v p := by
  let P : Process (E := E) F μ H → Process (E := E) F μ H := HeatPredictableGate.gate F μ H _ hs
  let N := HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I)
  have hPAB : P (A-B)=0 := by
    apply HeatPredictableGate.eq_zero F μ H _ hs
    filter_upwards [hAB,ae_eq_of_ae_eq_trim (Lp.coeFn_sub A B)] with p hp hsub ht
    rw [hsub]
    change A p-B p=0
    exact sub_eq_zero.mpr (hp ht)
  have hd : (u-v)-N (u-v)=A-B := by
    have hnsub := HeatConvolutionAlgebra.sub F μ H S hS hcontr M hsem (I) u v
    change N (u-v)=N u-N v at hnsub
    rw [hnsub]
    change (u-v)-(N u-N v)=A-B
    have heq := congrArg₂ (fun x y : Process (E := E) F μ H => x-y) hu hv
    change u-v=A+N u-(B+N v) at heq
    calc
      _ = (A+N u-(B+N v))-(N u-N v) := congrArg (fun x => x-(N u-N v)) heq
      _ = A-B := by abel
  have hPd : P (u-v)=P (N (P (u-v))) := by
    have hh := congrArg P hd
    have hpsub := HeatPredictableGate.sub F μ H _ hs (u-v) (N (u-v))
    change P ((u-v)-N (u-v))=P (u-v)-P (N (u-v)) at hpsub
    rw [hpsub,hPAB,sub_eq_zero] at hh
    exact hh.trans (HeatConvolutionStopLocality.convolution_gate F μ H S hS hcontr M basis J hsem
      hlocal hversions hnull τ hτ hs (u-v))
  obtain ⟨γ,hγ,hsmall,_⟩ := HeatMomentWeights.exists_weight (‖M‖^2) 0
  have hN0 : N 0=0 := HeatConvolutionAlgebra.zero F μ H S hS hcontr M hsem (I)
  have hscale0 (c : ℝ) : PredictableExponential.scale F μ H c (0 : Process (E := E) F μ H)=0 := by
    simpa only [sub_self] using PredictableExponential.sub F μ H c (0 : Process (E := E) F μ H) 0
  have he := HeatVolterraFixedPoint.weighted_energy F μ H S hS hcontr M hsem (I) γ hγ (P (u-v)) 0
  change ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ) (N (P (u-v))-N 0)‖^2)≤_ at he
  rw [hN0,sub_zero,sub_zero] at he
  have hCm : 0≤‖M‖^2*HeatRegularKernel.mass γ :=
    mul_nonneg (sq_nonneg _) (HeatRegularKernel.mass_nonneg γ hγ)
  rw [←ENNReal.ofReal_mul hCm] at he
  have hr := ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCm (sq_nonneg _))).mp he).trans
    (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _))
  have hnorm : ‖PredictableExponential.scale F μ H (-γ) (P (u-v))‖≤
      ‖PredictableExponential.scale F μ H (-γ) (N (P (u-v)))‖ := by
    have hh := HeatPredictableGate.norm_le F μ H _ hs
      (PredictableExponential.scale F μ H (-γ) (N (P (u-v))))
    rw [HeatPredictableGate.scale] at hh
    change ‖PredictableExponential.scale F μ H (-γ) (P (N (P (u-v))))‖≤_ at hh
    rw [←hPd] at hh
    exact hh
  have hz : PredictableExponential.scale F μ H (-γ) (P (u-v))=0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (PredictableExponential.scale F μ H (-γ) (P (u-v))),
      norm_nonneg (PredictableExponential.scale F μ H (-γ) (N (P (u-v))))]
  have hP : P (u-v)=0 := by
    rw [←PredictableExponential.cancel' F μ H γ (P (u-v)),hz,hscale0]
  have hgate := HeatPredictableGate.gate_ae F μ H _ hs (u-v)
  change P (u-v)=ᵐ[energyMeasure μ H] _ at hgate
  rw [hP] at hgate
  filter_upwards [hgate,ae_eq_of_ae_eq_trim (Lp.coeFn_zero E 2 _),
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v)] with p hg hz hsub ht
  have ht' : p∈{p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0)<τ p.2} := ht
  rw [hz,indicator_of_mem ht',hsub] at hg
  exact sub_eq_zero.mp hg.symm

end HeatLocalUniqueness
#check @HeatLocalUniqueness.unique_before
#print HeatLocalUniqueness.unique_before
#print axioms HeatLocalUniqueness.unique_before
