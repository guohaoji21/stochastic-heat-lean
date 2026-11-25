import HeatControlledFixedPoint
import HeatVersionLp
import HeatMildSolution

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatControlledMild
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Nontrivial E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

theorem exists_solution (hzero : S 0=ContinuousLinearMap.id ℝ E)
    (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (U : ℝ≥0 → Ω → E) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) (g : E) :
    ∃ A u : Process (E := E) F μ H, ∃ V : ℝ≥0 → Lp E 2 μ,
      u=HeatVolterraForcing.orbit F μ H S hS hcontr g+A+
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u ∧
      Continuous V ∧ V 0=Lp.const 2 μ g ∧
      (∀ t, ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ V t=ᵐ[μ] Z) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t) ∧
      (∀ t, V t=ᵐ[μ] fun ω => S t g+
        HeatControlConvolution.value H S (HeatControlAdapted.clamp U H) t ω+
        I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω) := by
  obtain ⟨A,u,hu,hunique,X,hc,ha,hp,hAE,hrep,D,hDm,hD0,hB,hMax⟩ :=
    HeatControlledFixedPoint.exists_fixed_point F μ H S hS hcontr M hsem I hn U hU hE g
  let hm : ∀ t, StronglyMeasurable (X t) := fun t => (ha t).mono (F.le t)
  let Q := HeatVersionLp.value μ X hm D hDm hB
  let V : ℝ≥0 → Lp E 2 μ := fun t =>
    HeatMildSolution.value F μ H S hS hcontr M I g u t+Q t
  have hQ (t : ℝ≥0) : Q t=ᵐ[μ] X t := HeatVersionLp.value_ae μ X hm D hDm hB t
  have hcV : Continuous V := (HeatMildSolution.value_continuous F μ H S hS hcontr M I g u).add
    (HeatVersionLp.continuous μ X hm D hDm hD0 hB hc)
  have hQ0 : Q 0=0 := by
    apply Lp.ext
    filter_upwards [hQ 0,hrep 0,Lp.coeFn_zero E 2 μ] with ω hq hx hz
    rw [hq,hx,hz]
    simp only [HeatControlConvolution.value,HeatControlConvolution.raw,HeatVolterraKernel.raw,
      not_lt_zero,ite_false,integral_zero,Pi.zero_apply]
  have hv0 : V 0=Lp.const 2 μ g := by
    change HeatMildSolution.value F μ H S hS hcontr M I g u 0+Q 0=_
    rw [hQ0,add_zero,HeatMildSolution.initial_value F μ H S hS hcontr M I hzero g u]
  have hvadapt (t : ℝ≥0) : ∃ Z : Ω → E, StronglyMeasurable[F t] Z ∧ V t=ᵐ[μ] Z := by
    obtain ⟨Z,hZ,hZrep⟩ := HeatMildSolution.value_adapted F μ H S hS hcontr M I g u t
    refine ⟨fun ω => Z ω+X t ω,hZ.add (ha t),?_⟩
    filter_upwards [Lp.coeFn_add (HeatMildSolution.value F μ H S hS hcontr M I g u t) (Q t),hZrep,hQ t] with ω hsum hz hq
    change (HeatMildSolution.value F μ H S hS hcontr M I g u t+Q t) ω=_
    rw [hsum]
    exact congrArg₂ (·+·) hz hq
  have hvrep (t : ℝ≥0) : V t=ᵐ[μ] fun ω => S t g+
      HeatControlConvolution.value H S (HeatControlAdapted.clamp U H) t ω+
      I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u) ω := by
    filter_upwards [Lp.coeFn_add (HeatMildSolution.value F μ H S hS hcontr M I g u t) (Q t),
      Lp.coeFn_add (Lp.const 2 μ (S t g)) (I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)),
      Lp.coeFn_const 2 μ (S t g),hQ t,hrep t] with ω hv hm hc hq hx
    change (HeatMildSolution.value F μ H S hS hcontr M I g u t+Q t) ω=_
    rw [hv]
    change (Lp.const 2 μ (S t g)+I.integral (HeatVolterraSlice.slice F μ H S hS hcontr M t u)) ω+Q t ω=_
    rw [hm]
    simp only [Pi.add_apply]
    rw [hc,hq,hx]
    simp only [Function.const_apply]
    abel
  have hslices : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t,ω))=ᵐ[μ] V t := by
    have ho := Measure.ae_ae_of_ae_prod (HeatVolterraForcing.orbit_ae F μ H S hS hcontr g)
    have hA := Measure.ae_ae_of_ae_prod hAE
    have hN := HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u
    have hsum : ∀ᵐ p ∂energyMeasure μ H, u p=
        HeatVolterraForcing.orbit F μ H S hS hcontr g p+A p+
        HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u p := by
      have hadd := ae_eq_of_ae_eq_trim (Lp.coeFn_add
        (HeatVolterraForcing.orbit F μ H S hS hcontr g+A)
        (HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u))
      rw [← hu] at hadd
      filter_upwards [hadd,ae_eq_of_ae_eq_trim (Lp.coeFn_add
        (HeatVolterraForcing.orbit F μ H S hS hcontr g) A)] with p hh hh2
      rw [hh]
      exact congrArg (fun z : E => z+HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u p) hh2
    filter_upwards [ho,hA,hN,Measure.ae_ae_of_ae_prod hsum] with t ho hA hN hh
    filter_upwards [ho,hA,hN,hh,hrep t,hvrep t] with ω ho hA hN hh hX hV
    change HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I u (t,ω)=_ at hN
    change A (t,ω)=X t ω at hA
    rw [hV,hh,ho,hA,hN,hX]
  exact ⟨A,u,V,hu,hcV,hv0,hvadapt,hslices,hvrep⟩

end HeatControlledMild
#check @HeatControlledMild.exists_solution
#print HeatControlledMild.exists_solution
#print axioms HeatControlledMild.exists_solution
