import HeatBrownianContinuous56
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Independence.Basic
import BrownianMotion.Gaussian.BrownianMotion
import SHEStochastic.NullAugmentedIndependence
import BrownianMotion.StochasticIntegral.Predictable
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import HeatSingleBrownianInterval
import SHE.StandardTerminalLevy
import SHE.BrownianFiniteCovariance
import SHEStochastic.CenteredGaussianFiniteLaw


set_option autoImplicit false
noncomputable section
namespace HeatCanonicalWiener56
open MeasureTheory ProbabilityTheory
open scoped NNReal

local notation "P" => SHEStochastic.CanonicalBrownianMeasure.measure
local notation "X" => SHEStochastic.CanonicalBrownianMeasure.process

def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  SHEStochastic.CanonicalBrownianMeasure.preBrownian.mk X

theorem measurable_brownian (t : ℝ≥0) : Measurable (brownian t) :=
  SHEStochastic.CanonicalBrownianMeasure.preBrownian.measurable_mk t

theorem continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) :=
  SHEStochastic.CanonicalBrownianMeasure.preBrownian.continuous_mk ω

theorem preBrownian : IsPreBrownianReal brownian P :=
  SHEStochastic.CanonicalBrownianMeasure.preBrownian.congr
    (fun t => (SHEStochastic.CanonicalBrownianMeasure.preBrownian.mk_ae_eq t).symm)

def path (ω : ℝ≥0 → ℝ) : C(ℝ≥0, ℝ) := ⟨(brownian · ω), continuous_brownian ω⟩

theorem measurable_path : Measurable path := by
  have h : Measurable (fun ω : ℝ≥0 → ℝ =>
      (⟨fun t => brownian t ω, continuous_brownian ω⟩ : {f : ℝ≥0 → ℝ // Continuous f})) := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval measurable_brownian
  exact (MeasurableEquiv.continuousMapToFun ℝ≥0 ℝ).symm.measurable.comp h

def wienerMeasure : Measure C(ℝ≥0, ℝ) := Measure.map path P

def coordinate (t : ℝ≥0) (ω : C(ℝ≥0, ℝ)) : ℝ := ω t

theorem coordinate_measurable (t : ℝ≥0) : Measurable (coordinate t) :=
  (continuous_eval_const t).measurable

theorem coordinate_preBrownian : IsPreBrownianReal coordinate wienerMeasure where
  hasLaw I := by
    have hm : Measurable (fun ω : C(ℝ≥0, ℝ) => I.restrict (coordinate · ω)) := by
      apply Measurable.of_eval
      intro t
      exact coordinate_measurable t
    refine ⟨hm.aemeasurable, ?_⟩
    unfold wienerMeasure
    rw [Measure.map_map hm measurable_path]
    exact (preBrownian.hasLaw I).map_eq

end HeatCanonicalWiener56
#check @HeatCanonicalWiener56.coordinate_preBrownian
#print axioms HeatCanonicalWiener56.coordinate_preBrownian


set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

/- Adapted from MathFin CompletedSpace, Apache-2.0. -/
namespace HeatCompletedSpace56
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)

/-- The `P`-completion of the ambient σ-algebra: the sets that agree `P`-almost everywhere
with an `mΩ`-measurable set. -/
@[reducible] noncomputable def completedMeasurableSpace : MeasurableSpace Ω :=
  eventuallyMeasurableSpace mΩ (ae P)

/-- The completion of `P`, read as a measure on the completed σ-algebra. -/
noncomputable def completedMeasure : @Measure Ω (completedMeasurableSpace P) := P.completion

theorem ambient_le_completion : mΩ ≤ completedMeasurableSpace P :=
  fun _ hs => hs.nullMeasurableSet

theorem completion_trim_original : (completedMeasure P).trim (ambient_le_completion P) = P := by
  ext s hs
  rw [trim_measurableSet_eq (ambient_le_completion P) hs]
  rfl

theorem integral_completion_original {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    (∫ ω, f ω ∂completedMeasure P) = ∫ ω, f ω ∂P := by
  rw [integral_trim (ambient_le_completion P) hf,completion_trim_original]

/-- The same filtration `𝓕`, regarded as a filtration of the completed ambient σ-algebra. -/
noncomputable def completedAmbientFiltration (𝓕 : Filtration ℝ≥0 mΩ) :
    Filtration ℝ≥0 (completedMeasurableSpace P) where
  seq := fun t => 𝓕 t
  mono' := fun _ _ h => 𝓕.mono h
  le' := fun t => (𝓕.le t).trans (ambient_le_completion P)

instance completion_isProbabilityMeasure [IsProbabilityMeasure P] : IsProbabilityMeasure
    (completedMeasure P) :=
  ⟨by change P Set.univ = 1; exact measure_univ⟩

instance completedMeasure_isComplete : (completedMeasure P).IsComplete :=
  ⟨fun _ hs => NullMeasurableSet.of_null hs⟩


end HeatCompletedSpace56

namespace HeatIndepCompletion56
open MeasureTheory ProbabilityTheory HeatCompletedSpace56

/-- Independence between ambient-measurable sigma-algebras survives completion of the measure. -/
theorem indep_completed_measure {Ω : Type*} [m0 : MeasurableSpace Ω]
    {mA mB : MeasurableSpace Ω} {μ : @Measure Ω m0} (hA : mA ≤ m0) (hB : mB ≤ m0)
    (h : @Indep Ω mA mB m0 μ) :
    @Indep Ω mA mB (@completedMeasurableSpace Ω m0 μ) (@completedMeasure Ω m0 μ) := by
  have heq (s : Set Ω) (hs : MeasurableSet[m0] s) : (@completedMeasure Ω m0 μ) s = μ s := by
    rfl
  refine (@Indep_iff Ω mA mB (@completedMeasurableSpace Ω m0 μ) (@completedMeasure Ω m0 μ)).2 ?_
  intro A B hAm hBm
  rw [heq (A ∩ B) ((hA A hAm).inter (hB B hBm)), heq A (hA A hAm), heq B (hB B hBm)]
  exact (@Indep_iff Ω mA mB m0 μ).1 h A B hAm hBm

end HeatIndepCompletion56

#check @HeatIndepCompletion56.indep_completed_measure
#print axioms HeatIndepCompletion56.indep_completed_measure

namespace HeatIndepCompletion56
open MeasureTheory ProbabilityTheory HeatCompletedSpace56

/-- The law of a measurable random element is unchanged by completing its source measure. -/
theorem hasLaw_completed {Ω E : Type*} [m0 : MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure E} {X : Ω → E}
    (hX : Measurable X) (h : HasLaw X ν μ) :
    HasLaw X ν (completedMeasure μ) where
  aemeasurable := (hX.mono (ambient_le_completion μ) le_rfl).aemeasurable
  map_eq := by
    have heq : @Measure.map Ω E (completedMeasurableSpace μ) _ X (completedMeasure μ) =
        @Measure.map Ω E m0 _ X μ := by
      ext s hs
      rw [Measure.map_apply (hX.mono (ambient_le_completion μ) le_rfl) hs,
        Measure.map_apply hX hs]
      rfl
    exact heq.trans h.map_eq

end HeatIndepCompletion56

#check @HeatIndepCompletion56.hasLaw_completed
#print axioms HeatIndepCompletion56.hasLaw_completed

namespace HeatIndepCompletion56
open MeasureTheory ProbabilityTheory HeatCompletedSpace56
open scoped NNReal

/-- Completing the ambient measure preserves a filtered Brownian process. -/
theorem filtered_preBrownian_completed {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : @Measure Ω m0} {F : Filtration ℝ≥0 m0} {W : ℝ≥0 → Ω → ℝ}
    (hW : IsFilteredPreBrownian W F μ) :
    @IsFilteredPreBrownian Ω (completedMeasurableSpace μ) W
      (completedAmbientFiltration μ F) (completedMeasure μ) := by
  have hM (t : ℝ≥0) : Measurable (W t) :=
    ((hW.stronglyAdapted t).mono (F.le t)).measurable
  refine { hasLaw := ?_, stronglyAdapted := ?_, indep := ?_ }
  · intro I
    apply hasLaw_completed ?_ (hW.hasLaw I)
    apply Measurable.of_eval
    intro t
    exact hM t
  · exact hW.stronglyAdapted
  · intro s t hst
    have hsrc : MeasurableSpace.comap (W t - W s) (borel ℝ) ≤ m0 :=
      ((hM t).sub (hM s)).comap_le
    exact @indep_completed_measure Ω m0 (MeasurableSpace.comap (W t - W s) (borel ℝ))
      (F s) μ hsrc (F.le s) (hW.indep s t hst)

end HeatIndepCompletion56
#check @HeatIndepCompletion56.filtered_preBrownian_completed
#print axioms HeatIndepCompletion56.filtered_preBrownian_completed


set_option autoImplicit false
noncomputable section
namespace HeatNullAugmentation56
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [μ.IsComplete]

def nullSigma : MeasurableSpace Ω := MeasurableSpace.generateFrom {s : Set Ω | μ s = 0}

theorem nullSigma_le : nullSigma (μ := μ) ≤ m0 := by
  apply MeasurableSpace.generateFrom_le
  intro s hs
  exact measurableSet_of_null hs

def nullAugmentation (F : Filtration ℝ≥0 m0) : Filtration ℝ≥0 m0 :=
  F ⊔ Filtration.const ℝ≥0 (nullSigma (μ := μ)) nullSigma_le

theorem filtered_preBrownian_nullAugmentation {F : Filtration ℝ≥0 m0}
    {W : ℝ≥0 → Ω → ℝ} (hW : IsFilteredPreBrownian W F μ) :
    IsFilteredPreBrownian W (nullAugmentation (μ := μ) F) μ where
  toIsPreBrownianReal := hW.toIsPreBrownianReal
  stronglyAdapted := fun t => (hW.stronglyAdapted t).mono le_sup_left
  indep := fun s t hst => SHEStochastic.NullAugmentedIndependence.indep_sup_null μ (hW.indep s t hst)

end HeatNullAugmentation56
#check @HeatNullAugmentation56.filtered_preBrownian_nullAugmentation
#print axioms HeatNullAugmentation56.filtered_preBrownian_nullAugmentation


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace HeatIndepLimit
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Independence of real random variables from a fixed past sigma-algebra is
preserved by pointwise limits on a finite measure space. -/
theorem indep_of_pointwise_limit {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, Measurable[m0] (X n))
    (hY : Measurable[m0] Y)
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) m μ)
    (hlim : ∀ ω, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep (MeasurableSpace.comap Y inferInstance) m μ := by
  apply Indep.symm
  apply indep_comap_of_bcf (P := μ) hm (hY.aemeasurable (μ := μ))
  intro A hA f
  have hmeas (n : ℕ) : StronglyMeasurable[m0] (fun ω => f (X n ω)) :=
    (f.continuous.measurable.comp (hX n)).stronglyMeasurable
  have hint (n : ℕ) : Integrable (fun ω => f (X n ω)) μ :=
    Integrable.of_bound (hmeas n).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun ω => f.norm_coe_le_norm (X n ω))
  have heach (n : ℕ) :
      (∫ ω in A, f (X n ω) ∂μ) = μ.real A * ∫ ω, f (X n ω) ∂μ := by
    have hstrong : StronglyMeasurable[MeasurableSpace.comap (X n) inferInstance]
        (fun ω => f (X n ω)) :=
      (f.continuous.measurable.comp (comap_measurable (X n))).stronglyMeasurable
    have hc := condExp_indep_eq (hX n).comap_le hm hstrong (hind n)
    calc
      (∫ ω in A, f (X n ω) ∂μ) = ∫ ω in A, μ[(fun ω => f (X n ω)) | m] ω ∂μ :=
        (setIntegral_condExp hm (hint n) hA).symm
      _ = ∫ ω in A, (∫ ω, f (X n ω) ∂μ) ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hc)
      _ = μ.real A * ∫ ω, f (X n ω) ∂μ := by simp [smul_eq_mul]
  have hfull : Tendsto (fun n => ∫ ω, f (X n ω) ∂μ) atTop
      (𝓝 (∫ ω, f (Y ω) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => f.norm_coe_le_norm (X n ω))
      (Eventually.of_forall fun ω => (f.continuous.tendsto (Y ω)).comp (hlim ω))
  have hrestrict : Tendsto (fun n => ∫ ω in A, f (X n ω) ∂μ) atTop
      (𝓝 (∫ ω in A, f (Y ω) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (hmeas n).aestronglyMeasurable.restrict) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => f.norm_coe_le_norm (X n ω))
      (Eventually.of_forall fun ω => (f.continuous.tendsto (Y ω)).comp (hlim ω))
  have hright : Tendsto (fun n => μ.real A * ∫ ω, f (X n ω) ∂μ) atTop
      (𝓝 (μ.real A * ∫ ω, f (Y ω) ∂μ)) := tendsto_const_nhds.mul hfull
  have hright' : Tendsto (fun n => ∫ ω in A, f (X n ω) ∂μ) atTop
      (𝓝 (μ.real A * ∫ ω, f (Y ω) ∂μ)) := by
    simpa only [heach] using hright
  exact tendsto_nhds_unique hrestrict hright'

end HeatIndepLimit
#check @HeatIndepLimit.indep_of_pointwise_limit
#print axioms HeatIndepLimit.indep_of_pointwise_limit

namespace HeatRightContBrownian
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
noncomputable def localizationEps (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem localizationEps_pos (n : ℕ) : 0 < localizationEps n := by
  unfold localizationEps
  positivity

theorem localizationEps_tendsto : Tendsto localizationEps atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
open scoped NNReal Topology

/-- Continuous filtered Brownian paths remain filtered Brownian after right continuation. -/
theorem filtered_preBrownian_rightCont {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 m0}
    {W : ℝ≥0 → Ω → ℝ} (hW : IsFilteredPreBrownian W F μ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) :
    IsFilteredPreBrownian W F.rightCont μ := by
  have hM (t : ℝ≥0) : Measurable[m0] (W t) :=
    ((hW.stronglyAdapted t).mono (F.le t)).measurable
  refine { hasLaw := hW.hasLaw, stronglyAdapted := ?_, indep := ?_ }
  · intro t
    exact (hW.stronglyAdapted t).mono (F.le_rightCont t)
  · intro s t hst
    rcases hst.eq_or_lt with heq | hlt
    · subst t
      rw [sub_self]
      change Indep (MeasurableSpace.comap (fun _ : Ω => (0 : ℝ)) (borel ℝ)) (F.rightCont s) μ
      rw [MeasurableSpace.comap_const]
      exact indep_bot_left (F.rightCont s)
    let u : ℕ → ℝ≥0 := fun n => min t (s + (localizationEps n).toNNReal)
    have hsu (n : ℕ) : s < u n := lt_min hlt
      (lt_add_of_pos_right s (Real.toNNReal_pos.mpr (localizationEps_pos n)))
    have hut (n : ℕ) : u n ≤ t := min_le_left _ _
    have hu : Tendsto u atTop (𝓝 s) := by
      have heps : Tendsto (fun n => (localizationEps n).toNNReal) atTop (𝓝 0) := by
        have htime : Continuous (fun x : ℝ => x.toNNReal) := by fun_prop
        convert! (htime.tendsto 0).comp localizationEps_tendsto using 1
        simp
      simpa only [u, add_zero, min_eq_right hst] using
        (tendsto_const_nhds (x := t)).min ((tendsto_const_nhds (x := s)).add heps)
    apply HeatIndepLimit.indep_of_pointwise_limit (F.rightCont.le s)
      (X := fun n => W t - W (u n)) (Y := W t - W s)
    · intro n
      exact (hM t).sub (hM (u n))
    · exact (hM t).sub (hM s)
    · intro n
      have hle : F.rightCont s ≤ F (u n) := by
        rw [Filtration.rightCont_eq]
        exact iInf₂_le (u n) (hsu n)
      exact indep_of_indep_of_le_right (hW.indep (u n) t (hut n)) hle
    · intro ω
      exact tendsto_const_nhds.sub (((hc ω).tendsto s).comp hu)

end HeatRightContBrownian
#check @HeatRightContBrownian.filtered_preBrownian_rightCont
#print axioms HeatRightContBrownian.filtered_preBrownian_rightCont


set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatFilteredBrownianFiniteLaw
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal

/-- A single filtered Brownian motion satisfies the finite-dimensional
conditions used to construct the terminal Itô integral, at any horizon. -/
theorem finite_law {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 m0} {W : ℝ≥0 → Ω → ℝ}
    (hW : IsFilteredPreBrownian W F μ) (T : ℝ≥0) (n : ℕ) (a : Fin n → Unit) :
    FiniteBrownianLawOn F μ T (fun _ => W)
      (fun i j => if a i = a j then 1 else 0) := by
  classical
  constructor
  · intro t ht
    let I : Finset ℝ≥0 := Finset.univ.image t
    let L0 : (I → ℝ) →L[ℝ] (Fin n → ℝ) := {
      toFun := fun x i => x ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
    let L : (I → ℝ) →L[ℝ] SHE.WordRecursion.State n :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp L0
    have hg : HasGaussianLaw (fun ω => WithLp.toLp 2 (fun i => W (t i) ω)) μ := by
      have hg' := (hW.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw I).map L
      convert hg' using 1
      funext ω
      apply PiLp.ext
      intro i
      rfl
    have hl := SHEStochastic.CenteredGaussianFiniteLaw.law_state
      (fun ω => WithLp.toLp 2 (fun i => W (t i) ω)) hg (BrownianFiniteCovariance.matrix a t)
      (BrownianFiniteCovariance.posSemidef a t)
      (fun i => hW.toIsPreBrownianReal.integral_eval (t i))
      (fun i j => by
        rw [hW.toIsPreBrownianReal.covariance_fun_eval]
        simp [BrownianFiniteCovariance.matrix])
    change HasLaw (fun ω => WithLp.toLp 2 (fun i => W (t i) ω))
      (multivariateGaussian (0 : SHE.WordRecursion.State n) (BrownianFiniteCovariance.matrix a t)) μ
    exact hl
  · intro s t hst ht
    let v : ℝ → SHE.WordRecursion.State n := fun x => WithLp.toLp 2 (fun _ : Fin n => x)
    have hv : Measurable v := (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (measurable_pi_iff.mpr (fun _ => measurable_id))
    have heq : (fun ω => WithLp.toLp 2 (fun _ : Fin n => W t ω - W s ω)) =
        v ∘ (W t - W s) := rfl
    rw [heq, ← MeasurableSpace.comap_comp]
    exact indep_of_indep_of_le_left (hW.indep s t hst)
      (MeasurableSpace.comap_mono hv.comap_le)

end HeatFilteredBrownianFiniteLaw
#check @HeatFilteredBrownianFiniteLaw.finite_law
#print axioms HeatFilteredBrownianFiniteLaw.finite_law

namespace HeatAnyFilteredBrownianInterval
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ≥0)
  (b : HilbertBasis κ ℝ E) (e : HilbertBasis Unit ℝ (Space Unit ℝ))
  (W : ℝ≥0 → Ω → ℝ)

theorem exists_integral_with_interval_cross
    (hW : IsFilteredPreBrownian W F μ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) :
    letI : MeasurableSpace (Space Unit ℝ) := borel _
    letI : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
    ∃ J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T,
      StandardTerminalPastLocality J ∧
      (∀ t : ℝ≥0, t ≤ T →
        J.integral (StoppedItoInputs.stop F μ T t
          (RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) ())) =ᵐ[μ] W t) ∧
      ∀ (a c : ℝ≥0), a ≤ c → ∀ (u v : Process (E := Space Unit E) F μ T),
        μ[(fun ω => inner ℝ
          ((SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T c u) ω -
            (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T a u) ω)
          ((SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T c v) ω -
            (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T a v) ω)) | F a] =ᵐ[μ]
        μ[(fun ω => ∫ t in Set.Ioc a c, inner ℝ (u (t, ω)) (v (t, ω)) ∂timeMeasure T) | F a] := by
  apply HeatSingleBrownianInterval.exists_integral_with_interval_cross F μ T b e W hc
  · intro t
    exact (hW.stronglyAdapted t).measurable
  · intro n a
    exact HeatFilteredBrownianFiniteLaw.finite_law hW T n a

end HeatAnyFilteredBrownianInterval
#check @HeatAnyFilteredBrownianInterval.exists_integral_with_interval_cross
#print axioms HeatAnyFilteredBrownianInterval.exists_integral_with_interval_cross

namespace HeatCanonicalUsual56
open MeasureTheory ProbabilityTheory HeatCompletedSpace56
open scoped NNReal
local notation "P" => HeatCanonicalWiener56.wienerMeasure
local notation "W" => HeatCanonicalWiener56.coordinate

def naturalFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) :=
  Filtration.natural W (fun t => (HeatCanonicalWiener56.coordinate_measurable t).stronglyMeasurable)

def usualFiltration : Filtration ℝ≥0 (completedMeasurableSpace P) :=
  (@HeatNullAugmentation56.nullAugmentation C(ℝ≥0, ℝ) (completedMeasurableSpace P)
    (completedMeasure P) (completedMeasure_isComplete P)
    (completedAmbientFiltration P naturalFiltration)).rightCont

theorem rightContinuous : usualFiltration.IsRightContinuous := by
  unfold usualFiltration
  infer_instance

theorem complete : usualFiltration.IsComplete (completedMeasure P) := by
  constructor
  intro s hs t
  apply (@HeatNullAugmentation56.nullAugmentation C(ℝ≥0, ℝ) (completedMeasurableSpace P)
    (completedMeasure P) (completedMeasure_isComplete P)
    (completedAmbientFiltration P naturalFiltration)).le_rightCont t
  apply (show @HeatNullAugmentation56.nullSigma C(ℝ≥0, ℝ) (completedMeasurableSpace P)
      (completedMeasure P) ≤
    @HeatNullAugmentation56.nullAugmentation C(ℝ≥0, ℝ) (completedMeasurableSpace P)
      (completedMeasure P) (completedMeasure_isComplete P)
      (completedAmbientFiltration P naturalFiltration) t from le_sup_right)
  exact MeasurableSpace.measurableSet_generateFrom hs

theorem coordinate_filtered_brownian :
    @IsFilteredPreBrownian C(ℝ≥0, ℝ) (completedMeasurableSpace P) W usualFiltration
      (completedMeasure P) := by
  letI : IsProbabilityMeasure P := HeatCanonicalWiener56.coordinate_preBrownian.isGaussianProcess.isProbabilityMeasure
  have hnatural : IsFilteredPreBrownian W naturalFiltration P :=
    HeatCanonicalWiener56.coordinate_preBrownian.isFilteredPreBrownian
      HeatCanonicalWiener56.coordinate_measurable
  have hcompleted := HeatIndepCompletion56.filtered_preBrownian_completed hnatural
  have hnull := @HeatNullAugmentation56.filtered_preBrownian_nullAugmentation
    C(ℝ≥0, ℝ) (completedMeasurableSpace P) (completedMeasure P) (completedMeasure_isComplete P)
    (completedAmbientFiltration P naturalFiltration) W hcompleted
  have hprob : IsProbabilityMeasure (completedMeasure P) := inferInstance
  have hright := @HeatRightContBrownian.filtered_preBrownian_rightCont
    C(ℝ≥0, ℝ) (completedMeasurableSpace P) (completedMeasure P) hprob
    (@HeatNullAugmentation56.nullAugmentation C(ℝ≥0, ℝ) (completedMeasurableSpace P)
      (completedMeasure P) (completedMeasure_isComplete P)
      (completedAmbientFiltration P naturalFiltration)) W hnull (fun ω => ω.continuous)
  exact hright

end HeatCanonicalUsual56
#check @HeatCanonicalUsual56.rightContinuous
#print axioms HeatCanonicalUsual56.rightContinuous
#check @HeatCanonicalUsual56.complete
#print axioms HeatCanonicalUsual56.complete
#check @HeatCanonicalUsual56.coordinate_filtered_brownian
#print axioms HeatCanonicalUsual56.coordinate_filtered_brownian

namespace HeatCanonicalUsualCross56
open MeasureTheory ProbabilityTheory HeatCompletedSpace56
open SHE SHE.PredictableL2 SHE.PastItoInputs SHE.HilbertColumns
open scoped NNReal ENNReal

def completedWiener : @Measure C(ℝ≥0, ℝ)
    (completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure) :=
  completedMeasure HeatCanonicalWiener56.wienerMeasure

theorem completedWiener_probability : IsProbabilityMeasure completedWiener := by
  letI : IsProbabilityMeasure HeatCanonicalWiener56.wienerMeasure :=
    HeatCanonicalWiener56.coordinate_preBrownian.isGaussianProcess.isProbabilityMeasure
  change IsProbabilityMeasure (completedMeasure HeatCanonicalWiener56.wienerMeasure)
  exact completion_isProbabilityMeasure _

local notation "F" => HeatCanonicalUsual56.usualFiltration
local notation "μ" => completedWiener
local notation "W" => HeatCanonicalWiener56.coordinate

variable {κ E : Type*} [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (T : ℝ≥0) (b : HilbertBasis κ ℝ E) (e : HilbertBasis Unit ℝ (Space Unit ℝ))

theorem canonical_interval_cross :
    letI : MeasurableSpace C(ℝ≥0, ℝ) := completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
    letI : IsProbabilityMeasure μ := completedWiener_probability
    letI : MeasurableSpace (Space Unit ℝ) := borel _
    letI : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
    ∃ J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T,
      StandardTerminalPastLocality J ∧
      (∀ t : ℝ≥0, t ≤ T →
        J.integral (StoppedItoInputs.stop F μ T t
          (RawCylindricalCoordinates.row F μ T (e : Unit → Space Unit ℝ) ())) =ᵐ[μ] W t) ∧
      ∀ (a c : ℝ≥0), a ≤ c → ∀ (u v : Process (E := Space Unit E) F μ T),
        μ[(fun ω => inner ℝ
          ((SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T c u) ω -
            (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T a u) ω)
          ((SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T c v) ω -
            (SHEStochastic.HilbertTerminalIto.terminalIto F μ T b J).integral (StoppedItoInputs.stop F μ T a v) ω)) | F a] =ᵐ[μ]
        μ[(fun ω => ∫ t in Set.Ioc a c, inner ℝ (u (t, ω)) (v (t, ω)) ∂SHE.PredictableL2.timeMeasure T) | F a] := by
  letI : MeasurableSpace C(ℝ≥0, ℝ) := completedMeasurableSpace HeatCanonicalWiener56.wienerMeasure
  letI : IsProbabilityMeasure μ := completedWiener_probability
  exact HeatAnyFilteredBrownianInterval.exists_integral_with_interval_cross F μ T b e W
    HeatCanonicalUsual56.coordinate_filtered_brownian (fun ω => ω.continuous)

end HeatCanonicalUsualCross56
#check @HeatCanonicalUsualCross56.canonical_interval_cross
#print axioms HeatCanonicalUsualCross56.canonical_interval_cross
