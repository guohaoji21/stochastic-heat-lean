import HeatTorusFixedBarrier
import HeatTorusSharpObservation
import HeatConstructedDuality
import HeatBackwardEndpointPairing
import HeatIntegralCauchy

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 4300000
noncomputable section

namespace HeatTorusNonzero

open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusCovarianceSeparation
open scoped NNReal ENNReal Topology

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

abbrev Control (O : Set (UnitAddTorus ι)) := Lp ℝ 2 ((volume : Measure (UnitAddTorus ι)).restrict O)

local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance (O : Set (UnitAddTorus ι)) : MeasurableSpace (Control O) := borel _
local instance (O : Set (UnitAddTorus ι)) : BorelSpace (Control O) := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance (O : Set (UnitAddTorus ι)) : SecondCountableTopology (Control O) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

variable {Ω κ : Type*} [MeasurableSpace Ω] [Countable κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : ℝ≥0) (basis : HilbertBasis κ ℝ (RealState ι)) (J : StandardTerminalIto
    (C := Space Unit ℝ) (E := ℝ) F μ T)

local notation "R" => RawCylindricalCoordinates.row F μ T (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()
local notation "I" => HeatTerminalNaturality.integral F μ T basis J

/-- A fixed positive endpoint pairing and arbitrarily small observation
energy exclude a zero terminal value for every finite-energy control. -/
theorem not_null_mild [Nontrivial (RealState ι)]
    (hT : 0 < T) (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (hP : 0 < P) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (hMsym : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0)
    (a : ℝ) (ha : 0 < a)
    (hmass : ∀ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t → t 0 = 0 → t N = T →
      a ≤ inner ℝ g (HeatBackwardChain.stateAt (K P M) (fun j => t j - t (j - 1)) N g 0))
    (U : ℝ≥0 × Ω → Control O) (hU : MemLp U 2 (energyMeasure μ T))
    (f : ℝ≥0 × Ω → RealState ι) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ T))
    (hforce : f =ᵐ[energyMeasure μ T] fun p => HeatRestrictionAdjoint.adjointExtension volume O (U p))
    (u : Process (E := RealState ι) F μ T) (V : ℝ≥0 → Lp (RealState ι) 2 μ)
    (hV : Continuous V) (hV0 : V 0 = Lp.const 2 μ g)
    (hVa : ∀ s, s ≤ T → AEStronglyMeasurable[F s] (V s) μ)
    (hVu : ∀ᵐ s ∂timeMeasure T, (fun ω => u (s, ω)) =ᵐ[μ] V s)
    (hy : ∀ a b : ℝ≥0, a ≤ b → b ≤ T → V b = (((family P) (b - a)).compLpL 2 μ) (V a) +
      HeatForwardDrift.value μ T (family P) (family_continuous P) (family_contraction P) f hf hfm a b +
      (I).integral (HeatMildKernelCross.forward F μ T (family P) (family_continuous P)
        (family_contraction P) M a b u)) : V T ≠ 0 := by
  intro hnull
  have hzero : family (ι := ι) P 0 = ContinuousLinearMap.id ℝ (RealState ι) := realHeat_zero P
  have hsem (s t : ℝ≥0) : family (ι := ι) P (s + t) = (family P s).comp (family P t) :=
    realHeat_add P s.property t.property
  have hsym (t : ℝ≥0) (x y : RealState ι) : inner ℝ (family P t x) y = inner ℝ x (family P t y) :=
    realHeat_symmetric P t x y
  obtain ⟨C, _, hC⟩ := HeatCompactLpBound.exists_bound μ T V hV
  let B := ‖g‖^2
  let E := ∫ p, ‖U p‖^2 ∂energyMeasure μ T
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨κ₀, hκ, hbound, _⟩ := HeatTorusSharpObservation.exists_sharp_offDiagonal hP O D hO hδ hsep
  have hineq (L : ℝ) (hL : 1 ≤ L) : a^2 ≤ E * (B * (2 * Real.exp (-κ₀ * L))) := by
    obtain ⟨t, N, ht, ht0, hN, htN, hstep, hobs⟩ := HeatTorusObservation.exists_grid_bound_of_bound
      F μ T J hT hlocal W hW hWa hWc P M hM O D zero_le_one hκ hbound hMsupp g hg L hL
    let z := HeatTorusObservation.path P M T W t N g
    let obs := fun p : ℝ≥0 × Ω => observe O (z p.1 p.2)
    have hp := HeatBrownianProducts.products_properties F μ T J hlocal W hW hWa t ht N
      (fun n hn => (ht hn).trans htN.le)
    let v := HeatBackwardNoise.process (family P) (family_continuous P) (family_contraction P) M F μ T W t N g hp
    obtain ⟨Z, _, hZrep, hZa, hzc, hza, ⟨A, hAm, hA0, hAb⟩, hz⟩ :=
      HeatBackwardLp.exists_solution F μ T (family P) (family_continuous P) (family_contraction P)
        M basis J hzero hsem hlocal W hW hWa hWc t ht ht0 N hN hstep htN g hp
    have hdual := HeatMildDuality.duality F μ T (family P) (family_continuous P) (family_contraction P)
      M basis J hzero hsem hsym hM hMsym hlocal f hf hfm V Z u v hV hVu C hC z hzc
      (fun s => (hza s).measurable.mono (F.le s) le_rfl) A hAm hA0 hAb hZrep hVa (fun s _ => hZa s) hy hz
    have hinit := HeatBackwardEndpointPairing.initial μ T (family P) (family_continuous P)
      (family_contraction P) M W t ht ht0 N hN hstep htN g g V Z hV0 (hZrep 0 zero_le)
    have hpair : (∫ p, inner ℝ (f p) (z p.1 p.2) ∂energyMeasure μ T) =
        ∫ p, inner ℝ (U p) (obs p) ∂energyMeasure μ T := by
      apply integral_congr_ae
      filter_upwards [hforce] with p hp'
      rw [hp', real_inner_comm (z p.1 p.2), ← HeatRestrictionAdjoint.restriction_adjoint_pairing]
      exact real_inner_comm (U p) (obs p)
    rw [hnull, inner_zero_left, hinit, hpair] at hdual
    change 0 = inner ℝ (HeatBackwardChain.stateAt (K P M) (fun j => t j - t (j - 1)) N g 0) g +
      (∫ p, inner ℝ (U p) (obs p) ∂energyMeasure μ T) at hdual
    have hmass' := (hmass t N ht ht0 htN).trans_eq (real_inner_comm _ _)
    have hlower : a ≤ -(∫ p, inner ℝ (U p) (obs p) ∂energyMeasure μ T) := by
      linarith [hdual, hmass']
    have hn : a^2 ≤ (∫ p, inner ℝ (U p) (obs p) ∂energyMeasure μ T)^2 := by
      nlinarith
    have hzpred := HeatBackwardProcess.predictable (family P) (family_continuous P)
      (family_contraction P) M F hzero W hWc hWa t ht ht0 N hN hstep htN.le g (fun n hn => (hp n hn).1)
    have hobsM : StronglyMeasurable obs :=
      (observe O).continuous.comp_stronglyMeasurable (hzpred.mono (predictable_le_product F))
    have hobsE := HeatTorusObservation.observation_integrable F μ T J hlocal W hW hWa hWc
      P M O t ht ht0 N hN htN hstep g
    have hobs₂ : MemLp obs 2 (energyMeasure μ T) :=
      (memLp_two_iff_integrable_sq_norm hobsM.aestronglyMeasurable).mpr hobsE
    exact hn.trans ((HeatIntegralCauchy.inner_square (energyMeasure μ T) U obs hU hobs₂).trans
      (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hobs) hE))
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hneg := hn.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ)
  have hlim : Tendsto (fun n : ℕ => E * (B * (2 * Real.exp (-κ₀ * ((n : ℝ) + 1)))))
      atTop (𝓝 0) := by
    simpa using (((Real.tendsto_exp_atBot.comp hneg).const_mul (2 : ℝ)).const_mul B).const_mul E
  have hle : a^2 ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun (n : ℕ) =>
    hineq ((n : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  exact (not_lt_of_ge hle) (sq_pos_of_pos ha)

end HeatTorusNonzero

#print axioms HeatTorusNonzero.not_null_mild
