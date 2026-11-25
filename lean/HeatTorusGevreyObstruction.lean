import HeatTorusGevreyDirichletData
import HeatTorusNonzero
import HeatCanonicalControlledHeat
import HeatFiniteControlExtension
import HeatTorusCanonicalIto

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 4500000
noncomputable section

namespace HeatTorusGevreyObstruction

open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusInitialData
open scoped NNReal ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P s : ℝ} {O : Set (ι → AddCircle P)}

local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance (D : Set (UnitAddTorus ι)) : MeasurableSpace (HeatTorusNonzero.Control D) := borel _
local instance (D : Set (UnitAddTorus ι)) : BorelSpace (HeatTorusNonzero.Control D) := ⟨rfl⟩
local instance (D : Set (UnitAddTorus ι)) : SecondCountableTopology (HeatTorusNonzero.Control D) :=
  Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate
local notation "Ω" => C(ℝ≥0, ℝ)

local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability

/-- The mild equation driven by the fixed coordinate Brownian motion. -/
structure MildSolution (P : ℝ) (T : ℝ≥0) (M : RealState ι →L[ℝ] RealState ι)
    (f : ℝ≥0 × Ω → RealState ι) (g : RealState ι) where
  process : Process (E := RealState ι) F μ T
  value : ℝ≥0 → Lp (RealState ι) 2 μ
  continuous_value : Continuous value
  initial_value : value 0 = Lp.const 2 μ g
  adapted_value : ∀ t, AEStronglyMeasurable[F t] (value t : Ω → RealState ι) μ
  slices : ∀ᵐ t ∂timeMeasure T, (fun ω => process (t, ω)) =ᵐ[μ] value t
  equation : ∀ t, value t =ᵐ[μ] fun ω => family P t g +
    HeatControlConvolution.value T (family P) f t ω +
    (HeatTorusCanonicalIto.integral ι T).integral
      (HeatVolterraSlice.slice F μ T (family P) (family_continuous P)
        (family_contraction P) M t process) ω

def CanonicalObstruction (hP : 0 < P) (d : HeatTorusGevreyData.Data hP s O) : Prop :=
  let D := rescale hP ⁻¹' O
  ∀ (T : ℝ≥0), 0 < T → ∀ U : ℝ≥0 → Ω → HeatTorusNonzero.Control D,
    HeatFiniteControlExtension.LocallyProgressive F T U →
    Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ T) →
    let force := HeatControlAdapted.clamp (fun t ω => HeatRestrictionAdjoint.adjointExtension volume D (U t ω)) T
    Nonempty (MildSolution P T d.multiplier force d.initial_value) ∧
      ∀ y : MildSolution P T d.multiplier force d.initial_value,
        0 < μ {ω | 0 < ‖y.value T ω‖}

/-- The fixed Gevrey data obstruct null control at every positive time
on the canonical completed Brownian space. -/
def Obstruction (hP : 0 < P) (d : HeatTorusGevreyData.Data hP s O) : Prop :=
  let D := rescale hP ⁻¹' O
  ∀ (T : ℝ≥0), 0 < T → ∀ U : ℝ≥0 → Ω → HeatTorusNonzero.Control D,
    HeatFiniteControlExtension.LocallyProgressive F T U →
    Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ T) →
    let force := HeatControlAdapted.clamp (fun t ω => HeatRestrictionAdjoint.adjointExtension volume D (U t ω)) T
    ∃ I : StandardTerminalIto (C := RealState ι) (E := RealState ι) F μ T,
      ∃ (u : Process (E := RealState ι) F μ T) (V : ℝ≥0 → Lp (RealState ι) 2 μ),
        Continuous V ∧ V 0 = Lp.const 2 μ d.initial_value ∧
        (∀ᵐ t ∂timeMeasure T, (fun ω => u (t, ω)) =ᵐ[μ] V t) ∧
        (∀ t, V t =ᵐ[μ] fun ω => family P t d.initial_value +
          HeatControlConvolution.value T (family P) force t ω +
          I.integral (HeatVolterraSlice.slice F μ T (family P) (family_continuous P)
            (family_contraction P) d.multiplier t u) ω) ∧
        0 < μ {ω | 0 < ‖V T ω‖}

theorem canonical_obstruction (hP : 0 < P) (hO : MeasurableSet O)
    (d : HeatTorusGevreyData.Data hP s O) : CanonicalObstruction hP d := by
  let : Nontrivial (RealState ι) := ⟨⟨d.initial_value, 0, d.initial_ne⟩⟩
  intro T hT U hU hE
  let basis := HeatTorusCanonicalIto.basis ι
  let J := HeatCanonicalNative.scalar T
  let I := HeatTerminalNaturality.integral F μ T basis J
  let O₀ := rescale hP ⁻¹' O
  let B := HeatRestrictionAdjoint.adjointExtension volume O₀
  let Ue := fun t ω => U (min t T) ω
  let Uf := fun t ω => B (Ue t ω)
  let f := HeatControlAdapted.clamp Uf T
  have hUe := HeatFiniteControlExtension.extend F T U hU
  have hUea := HeatFiniteControlExtension.energy_ae μ T U
  have hEe : Integrable (fun p : ℝ≥0 × Ω => ‖Ue p.1 p.2‖^2) (energyMeasure μ T) :=
    hE.congr (hUea.fun_comp (fun y => ‖y‖^2)).symm
  have hUf := HeatControlInjection.progressive F B Ue hUe
  have hEf := HeatControlInjection.energy F μ T B Ue hUe hEe
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F Uf hUf T).measurable
  have hfm := HeatClampedControl.square_integrable F μ T Uf hUf hEf
  have hforce : f =ᵐ[energyMeasure μ T] fun p => B (U p.1 p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem T)] with p hp
    simp only [f, HeatControlAdapted.clamp, Uf, Ue, min_eq_left hp.2]
  have hUm : AEStronglyMeasurable (Function.uncurry U) (energyMeasure μ T) :=
    (HeatControlAdapted.clamp_measurable F Ue hUe T).aestronglyMeasurable.congr (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem T)] with p hp
      simp only [HeatControlAdapted.clamp, Ue, min_eq_left hp.2]
      rfl)
  have hU₂ := (memLp_two_iff_integrable_sq_norm hUm).mpr hE
  have hzero : family (ι := ι) P 0 = ContinuousLinearMap.id ℝ (RealState ι) := realHeat_zero P
  have hsem (r t : ℝ≥0) : family (ι := ι) P (r + t) = (family P r).comp (family P t) :=
    realHeat_add P r.property t.property
  obtain ⟨_, u, V, _, hV, hV0, hVa, hVu, hVrep⟩ := HeatControlledMild.exists_solution F μ T
    (family P) (family_continuous P) (family_contraction P) d.multiplier hsem I hzero
    HeatCanonicalNullComplete.contains_nulls Uf hUf hEf d.initial_value
  have hfe : f = HeatControlAdapted.clamp (fun t ω => B (U t ω)) T := by
    funext p
    simp [f, HeatControlAdapted.clamp, Uf, Ue]
  refine ⟨⟨⟨u, V, hV, hV0, fun t => ?_, hVu, fun t => ?_⟩⟩, fun y => ?_⟩
  · obtain ⟨Y, hY, he⟩ := hVa t
    exact hY.aestronglyMeasurable.congr he.symm
  · rw [← hfe]
    exact hVrep t
  have hrep (t : ℝ≥0) : y.value t =ᵐ[μ] fun ω => family P t d.initial_value +
      HeatControlConvolution.value T (family P) f t ω +
      I.integral (HeatVolterraSlice.slice F μ T (family P) (family_continuous P)
        (family_contraction P) d.multiplier t y.process) ω := by
    rw [hfe]
    exact y.equation t
  have hy (r t : ℝ≥0) (hrt : r ≤ t) (_ : t ≤ T) :=
    HeatForwardLpEquation.equation F μ T (family P) (family_continuous P) (family_contraction P)
      d.multiplier basis J hsem f hf hfm d.initial_value y.process y.value hrep hrt
  have hWa : ∀ a, StronglyMeasurable[F a] (W a) :=
    HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted
  obtain ⟨a, ha, hmass⟩ := d.uniform_pairing T
  have hVne := HeatTorusNonzero.not_null_mild F μ T basis J hT (HeatCanonicalNative.locality T)
    W (HeatCanonicalNative.coordinate T) hWa (fun ω => ω.continuous) P hP d.multiplier d.multiplier_norm
    d.multiplier_symm O₀ d.support (hO.preimage (rescale hP).continuous.measurable) d.gap_pos d.separated
    d.multiplier_support d.initial_value d.initial_support a ha hmass
    (Function.uncurry U) hU₂ f hf hfm hforce y.process y.value y.continuous_value y.initial_value
    (fun t _ => y.adapted_value t) y.slices hy
  apply pos_iff_ne_zero.mpr
  intro hbad
  apply hVne
  have hae : ∀ᵐ ω ∂μ, ¬ 0 < ‖y.value T ω‖ := by
    rw [ae_iff]
    simpa only [not_not] using hbad
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero (RealState ι) 2 μ] with ω hω hzero'
  rw [hzero']
  exact norm_eq_zero.mp (le_antisymm (le_of_not_gt hω) (norm_nonneg _))

theorem obstruction (hP : 0 < P) (hO : MeasurableSet O)
    (d : HeatTorusGevreyData.Data hP s O) : Obstruction hP d := by
  intro T hT U hU hE
  obtain ⟨⟨y⟩, h⟩ := canonical_obstruction hP hO d T hT U hU hE
  exact ⟨HeatTorusCanonicalIto.integral ι T, y.process, y.value, y.continuous_value,
    y.initial_value, y.slices, y.equation, h y⟩

/-- The paper's superanalytic Gevrey counterexample, with the coefficient
and initial data chosen before the final time and the admissible control. -/
theorem gevrey_counterexample (hP : 0 < P) (hs : 1 < s) (hO : IsOpen O)
    {U : Set (ι → AddCircle P)} (hU : IsOpen U) (hgap : Disjoint U O)
    (c : ι → AddCircle P) (hc : c ∈ U) :
    ∃ d : HeatTorusGevreyData.Data hP s O, Obstruction hP d := by
  obtain ⟨d⟩ := HeatTorusGevreyData.exists_data hP hs hU hgap c hc
  exact ⟨d, obstruction hP hO.measurableSet d⟩

theorem paper_counterexample {n : ℕ} {O : Set (Fin n → AddCircle (2 * Real.pi))}
    (hs : 1 < s) (hO : IsOpen O) (c : Fin n → AddCircle (2 * Real.pi))
    {r : ℝ} (hr : 0 < r) (hgap : Metric.ball c r ⊆ Oᶜ) :
    ∃ d : HeatTorusGevreyData.Data (show 0 < 2 * Real.pi by positivity) s O,
      Obstruction (show 0 < 2 * Real.pi by positivity) d := by
  obtain ⟨_, _, _, _, _, _, _, _, d, _⟩ := HeatTorusGevreyDirichletData.exists_data (by positivity) hs
    Metric.isOpen_ball (disjoint_left.mpr fun _ hx hy => hgap hx hy) c (Metric.mem_ball_self hr)
  exact ⟨d, obstruction _ hO.measurableSet d⟩

/-- The Gevrey counterexample excludes null control for every mild solution
of the equation driven by the fixed canonical Brownian integral. -/
theorem paper_canonical_counterexample {n : ℕ} {O : Set (Fin n → AddCircle (2 * Real.pi))}
    (hs : 1 < s) (hO : IsOpen O) (c : Fin n → AddCircle (2 * Real.pi))
    {r : ℝ} (hr : 0 < r) (hgap : Metric.ball c r ⊆ Oᶜ) :
    ∃ d : HeatTorusGevreyData.Data (show 0 < 2 * Real.pi by positivity) s O,
      CanonicalObstruction (show 0 < 2 * Real.pi by positivity) d := by
  obtain ⟨_, _, _, _, _, _, _, _, d, _⟩ := HeatTorusGevreyDirichletData.exists_data (by positivity) hs
    Metric.isOpen_ball (disjoint_left.mpr fun _ hx hy => hgap hx hy) c (Metric.mem_ball_self hr)
  exact ⟨d, canonical_obstruction _ hO.measurableSet d⟩

end HeatTorusGevreyObstruction

#print axioms HeatTorusGevreyObstruction.canonical_obstruction
#print axioms HeatTorusGevreyObstruction.paper_canonical_counterexample
#print axioms HeatTorusGevreyObstruction.gevrey_counterexample
#print axioms HeatTorusGevreyObstruction.paper_counterexample
