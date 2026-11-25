import HeatTorusMildNullControl
import HeatTorusRealIntertwining
import HeatMildSpatialTransport
import HeatGevreyPeriodicHolomorphic
import HeatTorusCovarianceSeparation
import HeatTorusCanonicalIto

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section

namespace HeatTorusRealMildControl

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns UnitAddTorus
open HeatTorusReal (RealState embed realPart)
open HeatTorusRealIntertwining (Local localRealPart multiplier)
open HeatTorusCovarianceSeparation (family family_continuous family_contraction)
open HeatTorusProjectedConvolution (fullHeat fullHeat_continuous fullHeat_contraction)
open HeatTorusMildTerminalControl (state process input state_properties)
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Haar" => (volume : Measure (UnitAddTorus ι))
local notation "Full" => HeatTorusFourier.State ι
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology

local notation "Ω" => C(ℝ≥0, ℝ)
local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

/-- Itô integration in the real state space using the canonical scalar
coordinate Brownian motion. -/
def ito (ι : Type*) [Fintype ι] (H : ℝ≥0) :
    StandardTerminalIto (C := RealState ι) (E := RealState ι) F μ H :=
  HeatTorusCanonicalIto.integral ι H

/-- Null controllability by a real progressive drift control extended by
zero from the spatial control set, in the real mild equation. -/
def NullControllable (P : ℝ) (b : C(UnitAddTorus ι, ℂ)) (O : Set (UnitAddTorus ι)) (H : ℝ≥0) : Prop :=
  ∀ g : RealState ι, ∃ U : ℝ≥0 → Ω → Local O,
    IsStronglyProgressive F U ∧
    Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ H) ∧
    ∃ (w : Process (E := RealState ι) F μ H) (Y : ℝ≥0 → Lp (RealState ι) 2 μ),
        Continuous Y ∧ Y 0 = Lp.const 2 μ g ∧
        (∀ t, ∃ Z : Ω → RealState ι, StronglyMeasurable[F t] Z ∧ Y t =ᵐ[μ] Z) ∧
        (∀ᵐ t ∂timeMeasure H, (fun ω => w (t, ω)) =ᵐ[μ] Y t) ∧
        (∀ t, Y t =ᵐ[μ] fun ω => family P t g +
          HeatControlConvolution.value H (family P)
            (fun p => HeatRestrictionAdjoint.adjointExtension Haar O (U p.1 p.2)) t ω +
          (ito ι H).integral (HeatVolterraSlice.slice F μ H (family P) (family_continuous P)
            (family_contraction P) (multiplier b) t w) ω) ∧
        Y H = 0

theorem nullControllable {P C decay : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (ha : 0 < decay)
    (b : C(UnitAddTorus ι, ℂ)) (hb : ∀ x, (b x).im = 0)
    (hdec : ∀ k, ‖mFourierCoeff b k‖ ≤ C * Real.exp (-decay * HeatGevreyFourierExtension.weight k))
    {O : Set (UnitAddTorus ι)} (hO : IsOpen O) (hOne : O.Nonempty) {H : ℝ≥0} (hH : 0 < H) :
    NullControllable P b O H := by
  intro g
  obtain ⟨_, _, h⟩ := HeatTorusMildNullControl.exists_null_control hP hC ha b hb hdec hO hOne hH
  obtain ⟨u, _, hEnd⟩ := h (embed g)
  let A := realPart (ι := ι)
  let B := HeatRestrictionAdjoint.adjointExtension Haar O
  let v := HeatPredictableObservation.lift F μ H (localRealPart O) u
  let U := Function.curry (v : ℝ≥0 × Ω → Local O)
  let f := input O H u
  let q (p : ℝ≥0 × Ω) := B (v p)
  let X := state P b O H (embed g) u
  let x := process P b O H (embed g) u
  let w := HeatPredictableObservation.lift F μ H A x
  let Y (t : ℝ≥0) := (A.compLpL 2 μ) (X t)
  let β := HeatTorusCanonicalIto.basis ι
  let J := HeatCanonicalNative.scalar H
  let I := ito ι H
  have hp : IsStronglyPredictable F U := Lp.stronglyMeasurable v
  have hq : q =ᵐ[energyMeasure μ H] A ∘ f := by
    filter_upwards [HeatPredictableObservation.lift_ae F μ H (localRealPart O) u,
      HeatPredictableObservation.lift_ae F μ H (HeatTorusMildTerminalControl.injection O) u] with p hv hf
    change B (v p) = A (f p)
    change v p = _ at hv
    change f p = _ at hf
    rw [hv, hf]
    exact (HeatTorusRealIntertwining.extension_commutes hO.measurableSet (u p)).symm
  have hS (t : ℝ≥0) (z : Full) : A (fullHeat P t z) = family P t (A z) :=
    HeatTorusRealIntertwining.heat_commutes P t z
  obtain ⟨hXc, hX₀, hXa, hxs, hXrep⟩ := state_properties P b O H (embed g) u
  refine ⟨U, hp.isStronglyProgressive, (HeatPredictableObservation.ambient_memLp F μ H v).norm.integrable_sq,
    w, Y, (A.compLpL 2 μ).continuous.comp hXc, ?_, ?_, ?_, ?_, ?_⟩
  · change (A.compLpL 2 μ) (X 0) = _
    rw [show X 0 = Lp.const 2 μ (embed g) from hX₀]
    apply Lp.ext
    filter_upwards [A.coeFn_compLpL (Lp.const 2 μ (embed g)), Lp.coeFn_const 2 μ (embed g),
      Lp.coeFn_const 2 μ g] with ω h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    exact HeatTorusReal.realPart_embed g
  · intro t
    obtain ⟨Z, hZ, he⟩ := hXa t
    exact ⟨A ∘ Z, A.continuous.comp_stronglyMeasurable hZ,
      (A.coeFn_compLpL (X t)).trans (he.fun_comp A)⟩
  · have hw := HeatPredictableObservation.lift_ae F μ H A x
    filter_upwards [Measure.ae_ae_of_ae_prod hw, hxs] with t ht he
    have h₁ : (fun ω => w (t, ω)) =ᵐ[μ] fun ω => A (x (t, ω)) := ht
    have h₂ : (fun ω => x (t, ω)) =ᵐ[μ] X t := he
    exact h₁.trans ((h₂.fun_comp A).trans (A.coeFn_compLpL (X t)).symm)
  · intro t
    let M := HeatTorusGalerkinCompression.fullMultiplier b
    let N := multiplier b
    let d := HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P) M t x
    let e := HeatVolterraSlice.slice F μ H (family P) (family_continuous P) (family_contraction P) N t w
    let I₀ := HeatTorusMildTerminalControl.ito ι H
    have hd : (A.compLpL 2 μ) (I₀.integral d) = I.integral e := by
      change (A.compLpL 2 μ) ((HeatTerminalNaturality.integral F μ H
        (HeatTorusMildTerminalControl.basis ι) J).integral d) = _
      rw [HeatTerminalCrossNaturality.commutes F μ H (HeatTorusMildTerminalControl.basis ι) β J A]
      change I.integral (HeatPredictableObservation.lift F μ H A d) = I.integral e
      congr 1
      exact HeatMildSpatialTransport.slice F μ H (fullHeat P) (fullHeat_continuous P)
        (fullHeat_contraction P) (family P) (family_continuous P) (family_contraction P) A hS M N
        (HeatTorusRealIntertwining.multiplier_commutes b hb) t x
    have hC := HeatMildSpatialTransport.control_value μ H (fullHeat P) (fullHeat_continuous P)
      (fullHeat_contraction P) (family P) A hS f
      (HeatPredictableObservation.measurable_process F μ H f)
      (HeatPredictableObservation.ambient_memLp F μ H f) q hq t
    have hR : X t =ᵐ[μ] fun ω => fullHeat P t (embed g) +
      HeatControlConvolution.value H (fullHeat P) f t ω + I₀.integral d ω := hXrep t
    have hinit : A (embed g) = g := HeatTorusReal.realPart_embed g
    filter_upwards [A.coeFn_compLpL (X t), hR, hC, A.coeFn_compLpL (I₀.integral d)]
      with ω hy hx hqω hi
    change Y t ω = family P t g + HeatControlConvolution.value H (family P) q t ω + I.integral e ω
    change Y t ω = A (X t ω) at hy
    rw [hy, hx, map_add, map_add, hS, hinit, hqω, ← hi, hd]
  · change (A.compLpL 2 μ) (state P b O H (embed g) u H) = 0
    rw [hEnd, map_zero]

/-- The Gevrey-one positive conclusion on the physical-period torus.
The normalized Haar state and local control use the rescaled spatial
coordinate, with the same period in the heat generator. -/
theorem gevrey_one [Nonempty ι] [DecidableEq ι] {P : ℝ} (hP : 0 < P)
    (b : (ι → AddCircle P) → ℝ) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0))
    (hD : ∀ (l : List ι) x, |HeatGevreyProduct.mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x| ≤
      C * ρ ^ l.length * (l.length.factorial : ℝ))
    {O : Set (ι → AddCircle P)} (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ c : C(UnitAddTorus ι, ℂ), (∀ x, c x = (b (HeatTorusInitialData.rescale hP x) : ℂ)) ∧
      ∀ H : ℝ≥0, 0 < H → NullControllable P c (HeatTorusInitialData.rescale hP ⁻¹' O) H := by
  obtain ⟨c, hc, a, ha, hdec⟩ := HeatGevreyPeriodicHolomorphic.exists_coefficient_decay hP b C ρ hC hρ hb hD
  refine ⟨c, hc, fun H hH => nullControllable hP (by positivity) ha c (fun x => ?_) hdec
    (hO.preimage (HeatTorusInitialData.rescale hP).continuous) ?_ hH⟩
  · rw [hc, Complex.ofReal_im]
  · obtain ⟨x, hx⟩ := hOne
    refine ⟨(HeatTorusInitialData.rescale hP).symm x, ?_⟩
    simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hx

theorem paper_gevrey_one {n : ℕ} (hn : 0 < n) (b : (Fin n → AddCircle (2 * Real.pi)) → ℝ)
    {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0))
    (hD : ∀ (l : List (Fin n)) x, |HeatGevreyProduct.mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x| ≤
      C * ρ ^ l.length * (l.length.factorial : ℝ))
    {O : Set (Fin n → AddCircle (2 * Real.pi))} (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ c : C(UnitAddTorus (Fin n), ℂ),
      (∀ x, c x = (b (HeatTorusInitialData.rescale (show 0 < 2 * Real.pi by positivity) x) : ℂ)) ∧
      ∀ H : ℝ≥0, 0 < H → NullControllable (2 * Real.pi) c
        (HeatTorusInitialData.rescale (show 0 < 2 * Real.pi by positivity) ⁻¹' O) H := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact gevrey_one (by positivity) b hC.le hρ hb hD hO hOne

end HeatTorusRealMildControl

#print axioms HeatTorusRealMildControl.nullControllable
#print axioms HeatTorusRealMildControl.gevrey_one
#print axioms HeatTorusRealMildControl.paper_gevrey_one
