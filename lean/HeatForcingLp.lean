import HeatVersionLp
import HeatMildSolution

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatForcingLp
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nontrivial E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem exists_family (A u : Process (E := E) F μ H)
    (hu : u=A+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u)
    (G : ℝ≥0 → Ω → E) (hGc : ∀ ω, Continuous (fun t => G t ω)) (hGa : StronglyAdapted F G)
    (hAG : A=ᵐ[energyMeasure μ H] Function.uncurry G)
    (D : Ω → ℝ) (hDm : MemLp D 2 μ) (hD0 : ∀ ω, 0≤D ω) (hDb : ∀ t ω, ‖G t ω‖≤D ω) :
    ∃ V : ℝ≥0 → Lp E 2 μ, Continuous V ∧
      (∀ t, ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ V t=ᵐ[μ] Z) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t) ∧
      (∀ t, V t=ᵐ[μ] fun ω => G t ω+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) := by
  let hm : ∀ t, StronglyMeasurable (G t) := fun t => (hGa t).mono (F.le t)
  let Q := HeatVersionLp.value μ G hm D hDm hDb
  let V : ℝ≥0 → Lp E 2 μ := fun t => Q t+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)
  have hQ (t : ℝ≥0) : Q t=ᵐ[μ] G t := HeatVersionLp.value_ae μ G hm D hDm hDb t
  have hVc : Continuous V := (HeatVersionLp.continuous μ G hm D hDm hD0 hDb hGc).add
    (HeatVolterraContinuity.integral_continuous F μ H S hS hcontr M I u)
  have hVa (t : ℝ≥0) : ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ V t=ᵐ[μ] Z := by
    obtain ⟨Z,hZ,he⟩ := I.adapted t (HeatVolterraSlice.slice F μ H S hS hcontr M t u)
      (StoppedItoInputs.stop_stopped F μ H t _)
    refine ⟨fun ω => G t ω+Z ω,(hGa t).add hZ,?_⟩
    filter_upwards [Lp.coeFn_add (Q t) (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)),hQ t,he] with ω ha hq hz
    change (Q t+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)) ω=_
    rw [ha]
    exact congrArg₂ (·+·) hq hz
  have hrep (t : ℝ≥0) : V t=ᵐ[μ] fun ω => G t ω+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω := by
    filter_upwards [Lp.coeFn_add (Q t) (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)),hQ t] with ω ha hq
    change (Q t+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)) ω=_
    rw [ha]
    exact congrArg (fun z => z+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) hq
  have hsl : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t := by
    have ha := ae_eq_of_ae_eq_trim (Lp.coeFn_add A (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u))
    rw [←hu] at ha
    filter_upwards [Measure.ae_ae_of_ae_prod ha,Measure.ae_ae_of_ae_prod hAG,
      HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u] with t ha hag hc
    filter_upwards [ha,hag,hc,hrep t] with ω ha hag hc hv
    change HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω)=_ at hc
    rw [hv,ha]
    change A (t,ω)+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω)=_
    rw [hag,hc]
    rfl
  exact ⟨V,hVc,hVa,hsl,hrep⟩

end HeatForcingLp
#check @HeatForcingLp.exists_family
#print HeatForcingLp.exists_family
#print axioms HeatForcingLp.exists_family
