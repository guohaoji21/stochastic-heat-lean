import HeatPaperGevreyCorollary
import HeatTorusVariationalSolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace HeatPaperGevreyVariational

open Filter Set MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation HeatTorusProjectedConvolution
open HeatTorusGevreyObstruction (MildSolution CanonicalObstruction)
open HeatTorusInitialData (rescale)
open SHE.StoppedItoInputs
open scoped NNReal ENNReal

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
local instance (D : Set (UnitAddTorus ι)) : MeasurableSpace (HeatTorusRealIntertwining.Local D) := borel _
local instance (D : Set (UnitAddTorus ι)) : BorelSpace (HeatTorusRealIntertwining.Local D) := ⟨rfl⟩
local instance (D : Set (UnitAddTorus ι)) : SecondCountableTopology (HeatTorusRealIntertwining.Local D) :=
  Lp.SecondCountableTopology
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

private theorem real_state_nontrivial : Nontrivial (RealState ι) := by
  let ν : Measure (UnitAddTorus ι) := volume
  refine ⟨⟨Lp.const 2 ν (1 : ℝ), 0, ?_⟩⟩
  intro h
  have hc := Lp.coeFn_const 2 ν (1 : ℝ)
  rw [h] at hc
  have he := (Lp.coeFn_zero ℝ 2 ν).symm.trans hc
  have hf : ∀ᵐ ω ∂ν, False := he.mono (fun _ h => zero_ne_one h)
  have hz : ν Set.univ = 0 := by simpa only [ae_iff, not_false_eq_true, Set.setOf_true] using hf
  simpa [ν] using hz

/-- The Gevrey-one null control, expressed with variational solutions and
almost sure vanishing of the actual continuous path at the terminal time. -/
def NullControllable (P : ℝ) (b : C(UnitAddTorus ι, ℂ)) (O : Set (UnitAddTorus ι)) (T : ℝ≥0) : Prop :=
  ∀ g : RealState ι, ∃ U : ℝ≥0 → Ω → HeatTorusRealIntertwining.Local O,
    IsStronglyProgressive F U ∧
    Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ T) ∧
    ∃ z : HeatTorusVariationalSolution.Solution P T (HeatTorusRealIntertwining.multiplier b)
      (HeatControlAdapted.clamp (fun t ω => HeatRestrictionAdjoint.adjointExtension volume O (U t ω)) T) g,
      z.path T =ᵐ[μ] fun _ => 0

theorem nullControllable {P : ℝ} {T : ℝ≥0} (hT : 0 < T)
    {b : C(UnitAddTorus ι, ℂ)} {O : Set (UnitAddTorus ι)}
    (h : HeatTorusRealMildControl.NullControllable P b O T) : NullControllable P b O T := by
  let := real_state_nontrivial (ι := ι)
  intro g
  obtain ⟨U, hU, hE, w, V, hc, h0, ha, hs, he, hzero⟩ := h g
  let A := HeatRestrictionAdjoint.adjointExtension volume O
  let Uf (t : ℝ≥0) (ω : Ω) := A (U t ω)
  let f₀ := Function.uncurry Uf
  let f := HeatControlAdapted.clamp Uf T
  have hUf : IsStronglyProgressive F Uf := HeatControlInjection.progressive F A U hU
  have hEf := HeatControlInjection.energy F μ T A U hU hE
  have hfm := HeatClampedControl.square_integrable F μ T Uf hUf hEf
  have hf := (HeatControlAdapted.clamp_measurable F Uf hUf T).measurable
  have hff : f₀ =ᵐ[energyMeasure μ T] f := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem T)] with p hp
    change Uf p.1 p.2 = Uf (min p.1 T) p.2
    rw [min_eq_left hp.2]
  let y : MildSolution P T (HeatTorusRealIntertwining.multiplier b) f g := ⟨w, V, hc, h0,
    fun t => by
      obtain ⟨Z, hZa, hZ⟩ := ha t
      exact hZa.aestronglyMeasurable.congr hZ.symm,
    hs, fun t => by
      have hconv := HeatMildSpatialTransport.control_value μ T (family P) (family_continuous P)
        (family_contraction P) (family P) (ContinuousLinearMap.id ℝ (RealState ι)) (fun _ _ => rfl)
        f hf hfm f₀ hff t
      filter_upwards [he t, hconv] with ω hω hconv
      change HeatControlConvolution.value T (family P) f t ω =
         HeatControlConvolution.value T (family P) f₀ t ω at hconv
      change V t ω = family P t g + HeatControlConvolution.value T (family P) f t ω + _
      rw [hconv]
      exact hω⟩
  obtain ⟨z, hz⟩ := HeatTorusVariationalSolution.of_mild hT Uf hUf hEf y
  refine ⟨U, hU, hE, z, ?_⟩
  have he := z.path_value T le_rfl
  rw [hz, show y.value T = 0 from hzero] at he
  exact he.trans (Lp.coeFn_zero _ _ _)

variable [DecidableEq ι] {P s : ℝ} {O : Set (ι → AddCircle P)}

def Obstruction (hP : 0 < P) (d : HeatTorusGevreyData.Data hP s O) : Prop :=
  let D := rescale hP ⁻¹' O
  ∀ (T : ℝ≥0), 0 < T → ∀ U : ℝ≥0 → Ω → HeatTorusNonzero.Control D,
    HeatFiniteControlExtension.LocallyProgressive F T U →
    Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ T) →
    let f := HeatControlAdapted.clamp (fun t ω => HeatRestrictionAdjoint.adjointExtension volume D (U t ω)) T
    Nonempty (HeatTorusVariationalSolution.Solution P T d.multiplier f d.initial_value) ∧
      ∀ z : HeatTorusVariationalSolution.Solution P T d.multiplier f d.initial_value,
        0 < μ {ω | 0 < ‖z.path T ω‖}

theorem obstruction (hP : 0 < P) (d : HeatTorusGevreyData.Data hP s O)
    (h : CanonicalObstruction hP d) : Obstruction hP d := by
  intro T hT U hU hE
  let : Nontrivial (RealState ι) := ⟨⟨d.initial_value, 0, d.initial_ne⟩⟩
  let B := HeatRestrictionAdjoint.adjointExtension volume (rescale hP ⁻¹' O)
  let Ue (t : ℝ≥0) (ω : Ω) := U (min t T) ω
  let Uf (t : ℝ≥0) (ω : Ω) := B (Ue t ω)
  let f := HeatControlAdapted.clamp Uf T
  have hUe := HeatFiniteControlExtension.extend F T U hU
  have hUea := HeatFiniteControlExtension.energy_ae μ T U
  have hEe : Integrable (fun p : ℝ≥0 × Ω => ‖Ue p.1 p.2‖ ^ 2) (energyMeasure μ T) :=
    hE.congr (hUea.fun_comp (fun y => ‖y‖ ^ 2)).symm
  have hUf := HeatControlInjection.progressive F B Ue hUe
  have hEf := HeatControlInjection.energy F μ T B Ue hUe hEe
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F Uf hUf T).measurable
  have hfi := HeatClampedControl.square_integrable F μ T Uf hUf hEf
  have hfa := (HeatControlAdapted.clamp_progressive F Uf hUf T).stronglyAdapted
  have he : f = HeatControlAdapted.clamp (fun t ω => B (U t ω)) T := by
    funext p
    simp [f, HeatControlAdapted.clamp, Uf, Ue]
  have hc := h T hT U hU hE
  change Nonempty (MildSolution P T d.multiplier
      (HeatControlAdapted.clamp (fun t ω => B (U t ω)) T) d.initial_value) ∧
    (∀ y : MildSolution P T d.multiplier (HeatControlAdapted.clamp (fun t ω => B (U t ω)) T)
      d.initial_value, 0 < μ {ω | 0 < ‖y.value T ω‖}) at hc
  rw [← he] at hc ⊢
  obtain ⟨⟨y⟩, hy⟩ := hc
  obtain ⟨z, _⟩ := HeatTorusVariationalSolution.of_mild hT Uf hUf hEf y
  refine ⟨⟨z⟩, fun v => ?_⟩
  have hv := HeatTorusVariationalSolution.terminal_eq_mild hf hfi hfa y v
  have hset : {ω | 0 < ‖v.path T ω‖} =ᵐ[μ] {ω | 0 < ‖y.value T ω‖} :=
    hv.fun_comp (fun x => 0 < ‖x‖)
  rw [measure_congr hset]
  exact hy y

private abbrev period : ℝ := 2 * Real.pi
private theorem period_pos : 0 < period := by unfold period; positivity

/-- Both branches of the paper's Gevrey corollary, formulated on continuous
variational solutions of the periodic equation with their actual path endpoints. -/
theorem controllability_threshold {n : ℕ} (hn : 0 < n) {O : Set (Fin n → AddCircle period)}
    (hO : IsOpen O) (hOne : O.Nonempty) (c : Fin n → AddCircle period) {r : ℝ} (hr : 0 < r)
    (hgap : {x | HeatFlatTorusDistance.distance x c < r} ⊆ Oᶜ) :
    (∀ (b : (Fin n → AddCircle period) → ℝ) (C ρ : ℝ), 0 < C → 0 < ρ →
      ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0) →
      (∀ (l : List (Fin n)) x, |HeatGevreyProduct.mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x| ≤
        C * ρ ^ l.length * (l.length.factorial : ℝ)) →
      ∃ b₀ : C(UnitAddTorus (Fin n), ℂ), (∀ x, b₀ x = (b (rescale period_pos x) : ℂ)) ∧
        ∀ T : ℝ≥0, 0 < T → NullControllable period b₀ (rescale period_pos ⁻¹' O) T) ∧
    ∀ s : ℝ, 1 < s → ∃ d : HeatTorusGevreyData.Data period_pos s O, Obstruction period_pos d := by
  obtain ⟨h₁, h₂⟩ := HeatPaperGevreyCorollary.controllability_threshold hn hO hOne c hr hgap
  constructor
  · intro b C ρ hC hρ hreg hD
    obtain ⟨b₀, hb₀, h⟩ := h₁ b C ρ hC hρ hreg hD
    exact ⟨b₀, hb₀, fun t ht => nullControllable ht (h t ht)⟩
  · intro s hs
    obtain ⟨d, hd⟩ := h₂ s hs
    exact ⟨d, obstruction period_pos d hd⟩
end HeatPaperGevreyVariational

#print axioms HeatPaperGevreyVariational.nullControllable
#print axioms HeatPaperGevreyVariational.obstruction
#print axioms HeatPaperGevreyVariational.controllability_threshold
