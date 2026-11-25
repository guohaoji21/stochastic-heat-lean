import HeatHilbertRandomStop
import HeatPredictableGate
import HeatVolterraFixedPoint
import HeatVolterraContinuity

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatConvolutionStopLocality
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω E κ : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (basis : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "I" => HeatTerminalNaturality.integral F μ H basis J

theorem integral_eq_before (hlocal : StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u v : Process (E := E) F μ H) (T : ℝ≥0)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (huv : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 → u p=v p) :
    ∀ᵐ ω ∂μ, (T : WithTop ℝ≥0)≤τ ω →
      (I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M T u) ω=
        (I).integral (HeatVolterraSlice.slice F μ H S hS hcontr M T v) ω := by
  apply HeatHilbertRandomStop.integral_eq_before F μ H basis J hlocal hversions hnull
    (HeatPredictableStateInput.factor F μ H S hS hcontr M T u)
    (HeatPredictableStateInput.factor F μ H S hS hcontr M T v) T τ hτ
  filter_upwards [huv,HeatPredictableStateInput.factor_ae F μ H S hS hcontr M T u,
    HeatPredictableStateInput.factor_ae F μ H S hS hcontr M T v] with p hp hu hv ht
  rw [hu,hv,hp ht]

theorem convolution_gate (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
    (hlocal : StandardTerminalPastLocality J)
    (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (hs : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0)<τ p.2})
    (u : Process (E := E) F μ H) :
    HeatPredictableGate.gate F μ H _ hs (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I) u)=
      HeatPredictableGate.gate F μ H _ hs (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I)
        (HeatPredictableGate.gate F μ H _ hs u)) := by
  let P : Process (E := E) F μ H → Process (E := E) F μ H := HeatPredictableGate.gate F μ H _ hs
  let N := HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem (I)
  have he : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 → u p=P u p := by
    filter_upwards [HeatPredictableGate.gate_ae F μ H _ hs u] with p hp ht
    have ht' : p∈{p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0)<τ p.2} := ht
    exact (hp.trans (indicator_of_mem ht' _)).symm
  have hi (t : ℝ≥0) := integral_eq_before F μ H S hS hcontr M basis J hlocal hversions hnull
    u (P u) t τ hτ he
  apply PastItoAlgebra.eq_of_ambient_ae
  have hPm (w : Process (E := E) F μ H) : Measurable (fun p : ℝ≥0 × Ω => P w p) :=
    ((Lp.stronglyMeasurable (P w)).mono (predictable_le_product F)).measurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hPm (N u)) (hPm (N (P u))))).mpr
  filter_upwards [HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M (I) hsem u,
    HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M (I) hsem (P u),
    Measure.ae_ae_of_ae_prod (HeatPredictableGate.gate_ae F μ H _ hs (N u)),
    Measure.ae_ae_of_ae_prod (HeatPredictableGate.gate_ae F μ H _ hs (N (P u)))] with t hu hv hpu hpv
  filter_upwards [hu,hv,hpu,hpv,hi t] with ω hu hv hpu hpv hi
  change P (N u) (t,ω)=P (N (P u)) (t,ω)
  rw [hpu,hpv]
  by_cases ht : (t : WithTop ℝ≥0)<τ ω
  · have ht' : (t,ω)∈{p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0)<τ p.2} := ht
    rw [indicator_of_mem ht',indicator_of_mem ht']
    change N u (t,ω)=_ at hu
    change N (P u) (t,ω)=_ at hv
    exact hu.trans ((hi ht.le).trans hv.symm)
  · have ht' : (t,ω)∉{p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0)<τ p.2} := ht
    rw [indicator_of_notMem ht',indicator_of_notMem ht']

end HeatConvolutionStopLocality
#check @HeatConvolutionStopLocality.integral_eq_before
#print axioms HeatConvolutionStopLocality.integral_eq_before
#check @HeatConvolutionStopLocality.convolution_gate
#print HeatConvolutionStopLocality.convolution_gate
#print axioms HeatConvolutionStopLocality.convolution_gate
