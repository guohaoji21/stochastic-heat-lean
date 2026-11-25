import HeatTorusGevreyObstruction

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace HeatTorusStateObservability

open Filter MeasureTheory Set SHE SHE.PredictableL2 SHE.HilbertColumns
open UnitAddTorus HeatTorusReal HeatTorusInitialData HeatTorusCovarianceSeparation
open scoped NNReal ENNReal Topology

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => HeatCanonicalUsualCross56.completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate
local notation "Ω" => C(ℝ≥0, ℝ)

local instance : MeasurableSpace Ω :=
  HeatCompletedSpace56.completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
local instance : IsProbabilityMeasure μ := HeatCanonicalUsualCross56.completedWiener_probability
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P s : ℝ} {O : Set (ι → AddCircle P)}

local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

/-- The same Brownian-product adjoints violate each proposed observation inequality. -/
theorem exists_mild_counterexample (hP : 0 < P) (hO : MeasurableSet O)
    (d : HeatTorusGevreyData.Data hP s O) (T : ℝ≥0) (hT : 0 < T) (C : ℝ) (hC : 0 ≤ C) :
    let I := HeatTorusCanonicalIto.integral ι T
    let O₀ := rescale hP ⁻¹' O
    let M := d.multiplier
    let g := d.initial_value
    ∃ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t ∧ t 0 = 0 ∧ 1 ≤ N ∧ t N = T ∧
      (∀ n, n < N → t n < t (n + 1)) ∧
      ∃ hprod : ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (HeatBrownianProducts.products W t n) ∧
          MemLp (HeatBrownianProducts.products W t n) 2 μ,
        let z := HeatTorusObservation.path P M T W t N g
        let v := HeatBackwardNoise.process (family P) (family_continuous P) (family_contraction P)
          M F μ T W t N g hprod
        let q := HeatBackwardChain.stateAt (K P M) (fun j => t j - t (j - 1)) N g 0
        ∃ Z : ℝ≥0 → Lp (RealState ι) 2 μ, Continuous Z ∧
          (∀ a, a ≤ T → Z a =ᵐ[μ] z a) ∧ (∀ ω, z 0 ω = q) ∧
          (∀ ω, z T ω = HeatBrownianProducts.products W t N ω • g) ∧
          (∀ a b, a ≤ b → b ≤ T → Z a = ((family P (b-a)).compLpL 2 μ) (Z b) +
            HeatActualCellEnergy.drift F μ T (family P) (family_continuous P) (family_contraction P) M a b v -
            I.integral (HeatBackwardKernel.input F μ T (family P) (family_continuous P)
              (family_contraction P) (ContinuousLinearMap.id ℝ (RealState ι)) a b v)) ∧
          C * (∫ p : ℝ≥0 × Ω, ‖observe O₀ (z p.1 p.2)‖ ^ 2 ∂energyMeasure μ T) < ‖q‖ ^ 2 := by
  let : Nontrivial (RealState ι) := ⟨⟨d.initial_value, 0, d.initial_ne⟩⟩
  dsimp only
  let J := HeatCanonicalNative.scalar T
  let O₀ := rescale hP ⁻¹' O
  let g := d.initial_value
  have hWa : ∀ a, StronglyMeasurable[F a] (W a) :=
    HeatCanonicalUsual56.coordinate_filtered_brownian.stronglyAdapted
  obtain ⟨κ, hκ, hbound, _⟩ := HeatTorusSharpObservation.exists_sharp_offDiagonal hP O₀ d.support
    (hO.preimage (rescale hP).continuous.measurable) d.gap_pos d.separated
  obtain ⟨a, ha, hmass⟩ := d.uniform_pairing T
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hneg := hn.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ)
  have hlim : Tendsto (fun n : ℕ => (‖g‖ ^ 2 * C) * (‖g‖ ^ 2 * (2 * Real.exp (-κ * ((n : ℝ) + 1)))))
      atTop (𝓝 0) := by
    simpa using (((Real.tendsto_exp_atBot.comp hneg).const_mul (2 : ℝ)).const_mul (‖g‖ ^ 2)).const_mul (‖g‖ ^ 2 * C)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 _ (sq_pos_of_pos ha)).exists
  obtain ⟨t, N, ht, ht0, hN, htN, hstep, hobs⟩ := HeatTorusObservation.exists_grid_bound_of_bound
    F μ T J hT (HeatCanonicalNative.locality T) W (HeatCanonicalNative.coordinate T) hWa
    (fun ω => ω.continuous) P d.multiplier d.multiplier_norm O₀ d.support zero_le_one hκ hbound
    d.multiplier_support g d.initial_support ((n : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hzero : family (ι := ι) P 0 = ContinuousLinearMap.id ℝ (RealState ι) := realHeat_zero P
  have hsem (r u : ℝ≥0) : family (ι := ι) P (r + u) = (family P r).comp (family P u) :=
    realHeat_add P r.property u.property
  have hp := HeatBrownianProducts.products_properties F μ T J (HeatCanonicalNative.locality T)
    W (HeatCanonicalNative.coordinate T) hWa t ht N (fun j hj => (ht hj).trans htN.le)
  obtain ⟨Z, hZ, hZrep, _, _, _, _, hZeq⟩ := HeatBackwardLp.exists_solution F μ T
    (family P) (family_continuous P) (family_contraction P) d.multiplier (HeatTorusCanonicalIto.basis ι)
    J hzero hsem (HeatCanonicalNative.locality T) W (HeatCanonicalNative.coordinate T) hWa
    (fun ω => ω.continuous) t ht ht0 N hN hstep htN g hp
  refine ⟨t, N, ht, ht0, hN, htN, hstep, hp, Z, hZ, hZrep, ?_, ?_, hZeq, ?_⟩
  · intro ω
    have hi := HeatBackwardProcess.initial (family P) (family_continuous P) (family_contraction P)
      d.multiplier (H := T) W t ht N hN (hstep 0 (by omega)) htN.le g ω
    simpa only [ht0, HeatTorusObservation.path, K, g] using hi
  · intro ω
    have hterm := HeatBackwardProcess.terminal (family P) (family_continuous P) (family_contraction P)
      d.multiplier (H := T) hzero W t N hN hstep g ω
    simpa only [htN] using hterm
  · let q := HeatBackwardChain.stateAt (K P d.multiplier) (fun j => t j - t (j - 1)) N g 0
    have hq : a ≤ inner ℝ g q := hmass t N ht ht0 htN
    have hnorm : a ^ 2 ≤ ‖g‖ ^ 2 * ‖q‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ ha.le (hq.trans (real_inner_le_norm g q)) 2
    by_contra! hbad
    have hmul := mul_le_mul_of_nonneg_left hbad (sq_nonneg ‖g‖)
    have hupper := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hobs)
      (mul_nonneg (sq_nonneg ‖g‖) hC)
    rw [← mul_assoc] at hmul
    exact (not_lt_of_ge (hnorm.trans (hmul.trans hupper))) hn

end HeatTorusStateObservability

#print axioms HeatTorusStateObservability.exists_mild_counterexample
