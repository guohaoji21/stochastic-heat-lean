import HeatTorusFiniteDeterministicAdditive
import HeatTorusGalerkinTerminalDuality
import HeatControlledMild
import HeatClampedControl
import HeatCompactLpBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace HeatTorusProjectedForward

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns SHE.StoppedItoInputs
open UnitAddTorus
open HeatTorusGalerkinBackward (State laplace multiplier)
open HeatTorusGalerkinProjection (analysis)
open HeatTorusProjectedConvolution
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Full" => HeatTorusFourier.State ι
local instance : MeasurableSpace Full := borel _
local instance : BorelSpace Full := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology Full := Lp.SecondCountableTopology
local instance (S : Finset (ι → ℤ)) : InnerProductSpace ℝ (State S) :=
  InnerProductSpace.rclikeToReal ℂ (State S)
local instance (S : Finset (ι → ℤ)) : MeasurableSpace (State S) := borel _
local instance (S : Finset (ι → ℤ)) : BorelSpace (State S) := ⟨rfl⟩

variable {Ω κ ℓ : Type*} [mΩ : MeasurableSpace Ω] [Countable κ] [Countable ℓ]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] [IsSeparable μ]
  (H : ℝ≥0) (S : Finset (ι → ℤ)) (P : ℝ)

local notation "A" => ContinuousLinearMap.restrictScalars ℝ (analysis S)
local notation "L" => ContinuousLinearMap.compLpL 2 μ (laplace S P)
local notation "ν" => Measure.trim (energyMeasure μ H) (predictable_le_product F)

omit [IsSeparable μ] in
private theorem control_value (f : ℝ≥0 × Ω → Full) (hf : Measurable f)
    (hfi : MemLp f 2 (energyMeasure μ H)) (t : ℝ≥0) :
    (fun ω => A (HeatControlConvolution.value H (fullHeat P) f t ω)) =ᵐ[μ]
      HeatControlConvolution.value H (finiteHeat S P) (A ∘ f) t := by
  filter_upwards [HeatControlConvolution.time_memLp μ H f hf hfi] with ω hω
  let r (s : ℝ≥0) := HeatControlConvolution.raw (fullHeat P) f t (s, ω)
  have hr : Integrable r (timeMeasure H) := by
    apply (hω.integrable one_le_two).norm.mono'
    · exact ((HeatControlConvolution.raw_measurable (fullHeat P) (fullHeat_continuous P)
        (fullHeat_contraction P) f hf t).comp
          (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable
    · exact Eventually.of_forall fun s =>
        HeatControlConvolution.raw_bound (fullHeat P) (fullHeat_contraction P) f t (s, ω)
  change A (∫ s, r s ∂timeMeasure H) =
    ∫ s, HeatControlConvolution.raw (finiteHeat S P) (A ∘ f) t (s, ω) ∂timeMeasure H
  rw [← (A).integral_comp_comm hr]
  apply integral_congr_ae (Eventually.of_forall _)
  intro s
  dsimp only [r, HeatControlConvolution.raw, HeatVolterraKernel.raw]
  by_cases hs : s < t
  · simp only [ite_eq_left hs, ContinuousLinearMap.id_apply, Function.comp_apply]
    exact analysis_heat S P (t - s) (f (s, ω))
  · simp only [ite_eq_right hs, map_zero]

omit [IsSeparable μ] in
private theorem orbit_additive (x : State S) (t : ℝ≥0) :
    Lp.const 2 μ (finiteHeat S P t x) = Lp.const 2 μ x +
      ∫ r, L (Lp.const 2 μ (finiteHeat S P r x)) ∂timeMeasure t := by
  let c := Lp.constL (E := State S) 2 μ ℝ
  have hi : Integrable (fun r => laplace S P (finiteHeat S P r x)) (timeMeasure t) := by
    apply (integrable_const (‖laplace S P‖ * ‖x‖)).mono'
    · exact ((laplace S P).continuous.comp (finiteHeat_continuous S P x)).aestronglyMeasurable
    · exact Eventually.of_forall fun r => ((laplace S P).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (finiteHeat_contraction S P r x) (norm_nonneg _))
  have hc (r : ℝ≥0) : L (Lp.const 2 μ (finiteHeat S P r x)) = c (laplace S P (finiteHeat S P r x)) := by
    apply Lp.ext
    filter_upwards [(laplace S P).coeFn_compLpL (Lp.const 2 μ (finiteHeat S P r x)),
      Lp.coeFn_const 2 μ (finiteHeat S P r x), Lp.coeFn_const 2 μ (laplace S P (finiteHeat S P r x))]
      with ω hL hr hl
    change L (Lp.const 2 μ (finiteHeat S P r x)) ω = (Lp.const 2 μ (laplace S P (finiteHeat S P r x))) ω
    rw [hL, hr, hl]
    rfl
  simp_rw [hc]
  rw [c.integral_comp_comm hi, HeatTorusFiniteHeatGenerator.integrated, map_sub]
  change c _ = c x + (c _ - c x)
  abel

/-- The projection of a mild trajectory solves the actual finite additive equation
with the projected full diffusion. -/
theorem exists_projected_trajectory (M : Full →L[ℝ] Full)
    (β : HilbertBasis κ ℝ Full) (γ : HilbertBasis ℓ ℝ (State S))
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (f : ℝ≥0 × Ω → Full) (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ H))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (g : Full) (u : Process (E := Full) F μ H) (V : ℝ≥0 → Lp Full 2 μ)
    (hVc : Continuous V) (hV0 : V 0 = Lp.const 2 μ g)
    (hVa : ∀ t, ∃ Z : Ω → Full, StronglyMeasurable[F t] Z ∧ V t =ᵐ[μ] Z)
    (hVu : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] V t)
    (hV : ∀ t, V t =ᵐ[μ] fun ω => fullHeat P t g +
      HeatControlConvolution.value H (fullHeat P) f t ω +
      (HeatTerminalNaturality.integral F μ H β J).integral
        (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P)
          M t u) ω) :
    ∃ X : HeatItoProductEnergy.Trajectory (HeatTerminalNaturality.integral F μ H γ J),
      (∀ t, X.state t = ((A).compLpL 2 μ) (V t)) ∧
      (∀ t, X.drift t = L (X.state t) + HeatTimeLpField.value μ (A ∘ f) t) ∧
      (∀ᵐ t ∂timeMeasure H, X.noise t = (((A).comp M).compLpL 2 μ) (V t)) := by
  let D := (A).comp M
  let a := (A).compLpL 2 μ
  let v : Process (E := State S) F μ H := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (D.compLpL 2 ν) u
  let I := HeatTerminalNaturality.integral F μ H γ J
  let x (t : ℝ≥0) := a (V t)
  let fS := A ∘ f
  have hfm : Measurable fS := (A).continuous.measurable.comp hf
  have hfiS : MemLp fS 2 (energyMeasure μ H) := (A).lipschitzWith.comp_memLp (map_zero A) hfi
  let w := HeatTorusFiniteDeterministicAdditive.value μ H S P fS hfm hfiS
  let q := HeatTimeLpField.value μ fS
  let z := HeatBackwardEquationEnergy.slice v
  let o (t : ℝ≥0) := Lp.const 2 μ (finiteHeat S P t (A g))
  let U (t : ℝ≥0) := HeatVolterraSlice.slice F μ H (finiteHeat S P) (finiteHeat_continuous S P)
    (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) t v
  let n (t : ℝ≥0) := I.integral (U t)
  have hv : Measurable (v : ℝ≥0 × Ω → State S) :=
    ((Lp.stronglyMeasurable v).mono (predictable_le_product F)).measurable
  have hvi : MemLp (v : ℝ≥0 × Ω → State S) 2 (energyMeasure μ H) :=
    memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  have hq := HeatTimeLpField.square_integrable μ fS hfm H hfiS
  have hz : MemLp z 2 (timeMeasure H) := HeatTimeLpField.square_integrable μ v hv H hvi
  have hzs : ∀ᵐ t ∂timeMeasure H, z t =ᵐ[μ] fun ω => v (t, ω) :=
    HeatTimeLpField.value_ae μ v hv H hvi
  obtain ⟨C, _, hC⟩ := HeatCompactLpBound.exists_bound μ H V hVc
  have hVs : MemLp V 2 (timeMeasure H) := by
    apply (memLp_const C).mono' hVc.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem H] with t ht
    exact hC t ht.2
  have hxs : MemLp x 2 (timeMeasure H) := a.lipschitzWith.comp_memLp (map_zero a) hVs
  have hLx : MemLp (fun t => L (x t)) 2 (timeMeasure H) := (L).lipschitzWith.comp_memLp (map_zero L) hxs
  have ha (t : ℝ≥0) : AEStronglyMeasurable[F t] (x t : Ω → State S) μ := by
    obtain ⟨Z, hm, he⟩ := hVa t
    exact ((A).continuous.comp_stronglyMeasurable hm).aestronglyMeasurable.congr
      (((A).coeFn_compLpL (V t)).trans (he.fun_comp A)).symm
  have hx0 : x 0 = Lp.const 2 μ (A g) := by
    change a (V 0) = _
    rw [hV0]
    apply Lp.ext
    filter_upwards [(A).coeFn_compLpL (Lp.const 2 μ g), Lp.coeFn_const 2 μ g,
      Lp.coeFn_const 2 μ (A g)] with ω ha hg hAg
    rw [ha, hg, hAg]
    rfl
  have hsplit (t : ℝ≥0) : x t = o t + w t + n t := by
    let nf := (HeatTerminalNaturality.integral F μ H β J).integral
      (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P)
        (fullHeat_contraction P) M t u)
    have hc : a nf = n t := HeatTorusProjectedConvolution.convolution_eq F μ H S P M β γ J t u
    apply Lp.ext
    filter_upwards [(A).coeFn_compLpL (V t), (A).coeFn_compLpL nf, hV t,
      control_value μ H S P f hf hfi t, Lp.coeFn_const 2 μ (finiteHeat S P t (A g)),
      HeatTorusFiniteDeterministicAdditive.value_ae μ H S P fS hfm hfiS t,
      Lp.coeFn_add (o t) (w t), Lp.coeFn_add (o t + w t) (n t)] with
      ω hX hn hV hcontrol ho hw h1 h2
    change x t ω = (o t + w t + n t) ω
    change x t ω = A (V t ω) at hX
    change a nf ω = A (nf ω) at hn
    rw [hc] at hn
    rw [hX, hV, h2, Pi.add_apply, h1, Pi.add_apply, ho, hw, hn, map_add, map_add]
    have hheat : A (fullHeat P t g) = finiteHeat S P t (A g) := analysis_heat S P t g
    rw [hheat, hcontrol]
    rfl
  have heq (t : ℝ≥0) (ht : t ≤ H) :
      x t = x 0 + HeatDeterministicPairing.cumulative (timeMeasure H)
        (fun r => L (x r) + q r) t + HeatStoppedPairing.value F μ H I v t := by
    have ho : Integrable o (timeMeasure t) := by
      apply (Lp.constL (E := State S) 2 μ ℝ).integrable_comp
      apply (integrable_const ‖A g‖).mono' (finiteHeat_continuous S P (A g)).aestronglyMeasurable
      exact Eventually.of_forall fun r => finiteHeat_contraction S P r (A g)
    have hw := ((HeatTorusFiniteDeterministicAdditive.square_integrable μ H S P fS hfm hfiS).mono_measure
      (HeatTimeRestriction.mono ht)).integrable one_le_two
    have hn : Integrable n (timeMeasure t) := I.integral.toContinuousLinearMap.integrable_comp
      (HeatSliceNorm.integrable F μ H (finiteHeat S P) (finiteHeat_continuous S P)
        (finiteHeat_contraction S P) (ContinuousLinearMap.id ℝ (State S)) v t)
    have hsum : (∫ r, L (x r) ∂timeMeasure t) =
        ((∫ r, L (o r) ∂timeMeasure t) + ∫ r, L (w r) ∂timeMeasure t) +
          ∫ r, L (n r) ∂timeMeasure t := by
      simp_rw [hsplit, map_add]
      have hoi : Integrable (fun r => L (o r)) (timeMeasure t) := (L).integrable_comp ho
      have hwi : Integrable (fun r => L (w r)) (timeMeasure t) := (L).integrable_comp hw
      have hni : Integrable (fun r => L (n r)) (timeMeasure t) := (L).integrable_comp hn
      have how : Integrable (fun r => L (o r) + L (w r)) (timeMeasure t) := hoi.add hwi
      rw [integral_add how hni, integral_add hoi hwi]
    unfold HeatDeterministicPairing.cumulative HeatStoppedPairing.value
    rw [HeatTimeRestriction.restrict_Iio ht, integral_add
      ((hLx.mono_measure (HeatTimeRestriction.mono ht)).integrable one_le_two)
      ((hq.mono_measure (HeatTimeRestriction.mono ht)).integrable one_le_two),
      HeatTimeLpDrift.integral_value μ H fS hfm hfiS ht, hsum, hsplit t, hx0]
    rw [show o t = Lp.const 2 μ (A g) + ∫ r, L (o r) ∂timeMeasure t from orbit_additive μ S P (A g) t,
      show w t = _ from HeatTorusFiniteDeterministicAdditive.additive μ H S P fS hfm hfiS ht,
      show n t = I.integral (stop F μ H t v) + ∫ r, L (n r) ∂timeMeasure t from
        HeatTorusFiniteStochasticAdditive.additive F μ H S P γ J v t]
    abel
  refine ⟨{
    state := x
    drift := fun t => L (x t) + q t
    noise := z
    process := v
    state_square := hxs
    drift_square := hLx.add hq
    noise_square := hz
    initial_adapted := ha 0
    drift_adapted := ?_
    noise_slices := hzs.mono (fun _ h => h.symm)
    equation := heq }, fun _ => rfl, fun _ => rfl, ?_⟩
  · apply Eventually.of_forall
    intro t
    have hft (r : ℝ≥0) : StronglyMeasurable[F r] (fun ω => fS (r, ω)) :=
      (A).continuous.comp_stronglyMeasurable (hfa r)
    exact (((laplace S P).continuous.comp_aestronglyMeasurable (ha t)).congr
      ((laplace S P).coeFn_compLpL (x t)).symm |>.add
        (HeatTimeLpDrift.adapted μ fS F hft t)).congr (Lp.coeFn_add _ _).symm
  · have hvu : (v : ℝ≥0 × Ω → State S) =ᵐ[energyMeasure μ H] fun p => D (u p) := by
      let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      exact ae_eq_of_ae_eq_trim (D.coeFn_compLpL u)
    filter_upwards [hzs, Measure.ae_ae_of_ae_prod hvu, hVu] with t hz hvu hu
    apply Lp.ext
    filter_upwards [hz, hvu, hu, D.coeFn_compLpL (V t)] with ω hz hvu hu hD
    change z t ω = ((D.compLpL 2 μ) (V t)) ω
    rw [hz, hvu, hu, hD]

/-- The Fourier projection of an actual controlled mild solution is an
additive Itô trajectory. Its diffusion includes the exact Galerkin defect. -/
theorem exists_trajectory (b : C(UnitAddTorus ι, ℂ))
    (β : HilbertBasis κ ℝ Full) (γ : HilbertBasis ℓ ℝ (State S))
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (f : ℝ≥0 × Ω → Full) (hf : Measurable f) (hfi : MemLp f 2 (energyMeasure μ H))
    (hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)))
    (g : Full) (u : Process (E := Full) F μ H) (V : ℝ≥0 → Lp Full 2 μ)
    (hVc : Continuous V) (hV0 : V 0 = Lp.const 2 μ g)
    (hVa : ∀ t, ∃ Z : Ω → Full, StronglyMeasurable[F t] Z ∧ V t =ᵐ[μ] Z)
    (hVu : ∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] V t)
    (hV : ∀ t, V t =ᵐ[μ] fun ω => fullHeat P t g +
      HeatControlConvolution.value H (fullHeat P) f t ω +
      (HeatTerminalNaturality.integral F μ H β J).integral
        (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P)
          (HeatTorusGalerkinCompression.fullMultiplier b) t u) ω) :
    ∃ X : HeatItoProductEnergy.Trajectory (HeatTerminalNaturality.integral F μ H γ J),
      (∀ t, X.state t = ((A).compLpL 2 μ) (V t)) ∧
      (∀ t, X.drift t = L (X.state t) + HeatTimeLpField.value μ (A ∘ f) t) ∧
      (∀ᵐ t ∂timeMeasure H, X.noise t = ((multiplier S b).compLpL 2 μ) (X.state t) +
        ((HeatTorusGalerkinTerminalDuality.diffusionResidual S b).compLpL 2 μ) (V t)) := by
  let M := HeatTorusGalerkinCompression.fullMultiplier b
  let D := (A).comp M
  let B := multiplier S b
  let R := HeatTorusGalerkinTerminalDuality.diffusionResidual S b
  obtain ⟨X, hx, hd, hn⟩ :=
    exists_projected_trajectory F μ H S P M β γ J f hf hfi hfa g u V hVc hV0 hVa hVu hV
  refine ⟨X, hx, hd, ?_⟩
  filter_upwards [hn] with t ht
  rw [ht, hx t]
  let x := ((A).compLpL 2 μ) (V t)
  apply Lp.ext
  filter_upwards [D.coeFn_compLpL (V t), (A).coeFn_compLpL (V t), B.coeFn_compLpL x,
    R.coeFn_compLpL (V t), Lp.coeFn_add ((B.compLpL 2 μ) x) ((R.compLpL 2 μ) (V t))]
    with ω hD hA hB hR hsum
  change ((D.compLpL 2 μ) (V t)) ω = ((B.compLpL 2 μ) x + (R.compLpL 2 μ) (V t)) ω
  change x ω = A (V t ω) at hA
  rw [hD, hsum, Pi.add_apply, hB, hA, hR]
  change D (V t ω) = B (A (V t ω)) + (D (V t ω) - B (A (V t ω)))
  abel

/-- Terminal duality for the actual controlled torus mild solution and every
finite backward solution driven by the same scalar noise. -/
theorem controlled_terminal_pairing (b : C(UnitAddTorus ι, ℂ)) (hb : ∀ p, (b p).im = 0)
    (β : HilbertBasis κ ℝ Full) (γ : HilbertBasis ℓ ℝ (State S))
    (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
    (hJ : StandardTerminalPastLocality J) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (U : ℝ≥0 → Ω → Full) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖ ^ 2) (energyMeasure μ H)) (g : Full) :
    ∃ u : Process (E := Full) F μ H, ∃ V : ℝ≥0 → Lp Full 2 μ,
      Continuous V ∧ V 0 = Lp.const 2 μ g ∧
      (∀ t, ∃ Z : Ω → Full, StronglyMeasurable[F t] Z ∧ V t =ᵐ[μ] Z) ∧
      (∀ᵐ t ∂timeMeasure H, (fun ω => u (t, ω)) =ᵐ[μ] V t) ∧
      (∀ t, V t =ᵐ[μ] fun ω => fullHeat P t g +
        HeatControlConvolution.value H (fullHeat P) (HeatControlAdapted.clamp U H) t ω +
        (HeatTerminalNaturality.integral F μ H β J).integral
          (HeatVolterraSlice.slice F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P)
            (HeatTorusGalerkinCompression.fullMultiplier b) t u) ω) ∧
      ∀ (η : Lp (State S) 2 μ)
        (Y : HeatLocalBackwardEquation.Solution (HeatTerminalNaturality.integral F μ H γ J)
          (laplace S P) (multiplier S b) 0 H η),
        inner ℝ (((A).compLpL 2 μ) (V H)) η =
          inner ℝ (((A).compLpL 2 μ) (V 0)) (HeatBackwardDriver.state H η Y.drift 0) +
          (∫ s, inner ℝ (HeatTimeLpField.value μ (A ∘ HeatControlAdapted.clamp U H) s)
            (HeatBackwardDriver.state H η Y.drift s) ∂timeMeasure H) +
          ∫ s, inner ℝ (((HeatTorusGalerkinTerminalDuality.diffusionResidual S b).compLpL 2 μ) (V s))
            (HeatBackwardEquationEnergy.slice Y.noise s) ∂timeMeasure H := by
  let f := HeatControlAdapted.clamp U H
  have hfm : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hf : MemLp f 2 (energyMeasure μ H) := HeatClampedControl.square_integrable F μ H U hU hE
  have hfa : ∀ t, StronglyMeasurable[F t] (fun ω => f (t, ω)) :=
    (HeatControlAdapted.clamp_progressive F U hU H).stronglyAdapted
  have hsem (s t : ℝ≥0) : fullHeat (ι := ι) P (s + t) = (fullHeat P s).comp (fullHeat P t) := by
    apply ContinuousLinearMap.ext
    intro x
    change HeatTorusFourier.heat P ((s : ℝ) + (t : ℝ)) x =
      HeatTorusFourier.heat P s (HeatTorusFourier.heat P t x)
    exact congrArg (fun (op : Full →L[ℂ] Full) => op x)
      (HeatTorusFourier.heat_add (ι := ι) P s.property t.property)
  have hzero : fullHeat (ι := ι) P 0 = ContinuousLinearMap.id ℝ Full := by
    apply ContinuousLinearMap.ext
    intro x
    change HeatTorusFourier.heat P 0 x = x
    rw [HeatTorusFourier.heat_zero]
    rfl
  let one : Full := Lp.const 2 (volume : Measure (UnitAddTorus ι)) (1 : ℂ)
  have hone : ‖one‖ = 1 := by
    change ‖Lp.const 2 (volume : Measure (UnitAddTorus ι)) (1 : ℂ)‖ = 1
    rw [Lp.norm_const _ _ _ (by norm_num), Measure.real, measure_univ, ENNReal.toReal_one,
      Real.one_rpow, mul_one, norm_one]
  let : Nontrivial Full := ⟨⟨one, 0, fun h => by
    rw [h, norm_zero] at hone
    exact zero_ne_one hone⟩⟩
  obtain ⟨_, u, V, _, hVc, hV0, hVa, hVu, hV⟩ :=
    HeatControlledMild.exists_solution F μ H (fullHeat P) (fullHeat_continuous P) (fullHeat_contraction P)
      (HeatTorusGalerkinCompression.fullMultiplier b) hsem (HeatTerminalNaturality.integral F μ H β J)
      hzero hn U hU hE g
  obtain ⟨X, hx, hd, hz⟩ :=
    exists_trajectory F μ H S P b β γ J f hfm hf hfa g u V hVc hV0 hVa hVu hV
  refine ⟨u, V, hVc, hV0, hVa, hVu, hV, ?_⟩
  intro η Y
  let R := (HeatTorusGalerkinTerminalDuality.diffusionResidual S b).compLpL 2 μ
  have hfS : MemLp (A ∘ f) 2 (energyMeasure μ H) := (A).lipschitzWith.comp_memLp (map_zero A) hf
  have hq := HeatTimeLpField.square_integrable μ (A ∘ f) ((A).continuous.measurable.comp hfm) H hfS
  obtain ⟨C, _, hC⟩ := HeatCompactLpBound.exists_bound μ H V hVc
  have hVs : MemLp V 2 (timeMeasure H) := by
    apply (memLp_const C).mono' hVc.aestronglyMeasurable
    filter_upwards [timeMeasure_ae_mem H] with t ht
    exact hC t ht.2
  have hr : MemLp (fun t => R (V t)) 2 (timeMeasure H) :=
    R.lipschitzWith.comp_memLp (map_zero R) hVs
  have h := HeatTorusGalerkinTerminalDuality.terminal_pairing
    (HeatTerminalNaturality.locality F μ H γ J hJ) hb Y X _ _ hq hr
    (Eventually.of_forall hd) hz
  rw [hx H, hx 0] at h
  exact h

end HeatTorusProjectedForward

#print axioms HeatTorusProjectedForward.exists_projected_trajectory
#print axioms HeatTorusProjectedForward.exists_trajectory
#print axioms HeatTorusProjectedForward.controlled_terminal_pairing
