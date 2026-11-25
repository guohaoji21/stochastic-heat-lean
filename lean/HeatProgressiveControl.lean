import HeatControlAdapted
import HeatControlContinuity
import HeatPathMaximum
import SHE.NullCompleteFiltration

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatProgressiveControl
open MeasureTheory SHE SHE.PredictableL2 HeatControlConvolution
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

include hS hcontr in
theorem exists_version (hn : NullCompleteFiltration.ContainsNullSets F μ) (U : ℝ≥0 → Ω → E) (hU : IsStronglyProgressive F U)
    (hE : Integrable (fun p : ℝ≥0 × Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    ∃ A : Process (E := E) F μ H, ∃ X : ℝ≥0 → Ω → E,
      (∀ ω, Continuous (fun t => X t ω)) ∧ StronglyAdapted F X ∧
      StronglyMeasurable[F.predictable] (Function.uncurry X) ∧
      (A=ᵐ[energyMeasure μ H] Function.uncurry X) ∧
      (∀ t, X t=ᵐ[μ] value H S (HeatControlAdapted.clamp U H) t) ∧
      ∃ D : Ω → ℝ, MemLp D 2 μ ∧ (∀ ω, 0≤D ω) ∧
        (∀ t ω, ‖X t ω‖≤D ω) ∧ Integrable (fun ω => HeatPathMaximum.value H X ω^2) μ := by
  classical
  let f := HeatControlAdapted.clamp U H
  have hf : Measurable f := (HeatControlAdapted.clamp_measurable F U hU H).measurable
  have hfeq : f=ᵐ[energyMeasure μ H] Function.uncurry U := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (timeMeasure_ae_mem H)] with p hp
    simp only [f,HeatControlAdapted.clamp,min_eq_left hp.2,Function.uncurry_apply_pair]
    rfl
  have hfm : MemLp f 2 (energyMeasure μ H) := by
    apply (memLp_two_iff_integrable_sq_norm hf.stronglyMeasurable.aestronglyMeasurable).mpr
    exact hE.congr (hfeq.fun_comp (fun z : E => ‖z‖^2)).symm
  have hfprog := HeatControlAdapted.clamp_progressive F U hU H
  let X : ℝ≥0 → Ω → E := fun t ω =>
    if MemLp (fun s => f (s,ω)) 2 (timeMeasure H) then value H S (HeatControlAdapted.clamp U H) t ω else 0
  have hXc (ω : Ω) : Continuous (fun t => X t ω) := by
    by_cases hω : MemLp (fun s => f (s,ω)) 2 (timeMeasure H)
    · simpa only [X,if_pos hω] using HeatControlContinuity.continuous_path H S hS hcontr f hf ω hω
    · simpa only [X,if_neg hω] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0:E)))
  have hrep (t : ℝ≥0) : X t=ᵐ[μ] value H S (HeatControlAdapted.clamp U H) t := by
    filter_upwards [time_memLp μ H f hf hfm] with ω hω
    simp only [X,if_pos hω]
  have hXa : StronglyAdapted F X := fun t =>
    NullCompleteFiltration.stronglyMeasurable_congr F μ hn t
      (HeatControlAdapted.adapted S hS hcontr F (fun t ω => f (t,ω)) hfprog H t) (hrep t)
  have hXp : StronglyMeasurable[F.predictable] (Function.uncurry X) :=
    ContinuousPredictable.stronglyMeasurable F X hXa hXc
  let Q : Ω → ℝ := fun ω => (H:ℝ)*(∫ s, ‖f (s,ω)‖^2 ∂timeMeasure H)
  have hQ0 (ω : Ω) : 0≤Q ω := mul_nonneg H.property (integral_nonneg (fun s => sq_nonneg _))
  have hQi : Integrable Q μ :=
    (hfm.norm.integrable_sq.integral_prod_right).const_mul (H:ℝ)
  let D : Ω → ℝ := fun ω => Real.sqrt (Q ω)
  have hD0 (ω : Ω) : 0≤D ω := Real.sqrt_nonneg _
  have hDm : MemLp D 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm (Real.continuous_sqrt.comp_aestronglyMeasurable hQi.aestronglyMeasurable)).mpr
    apply hQi.congr
    filter_upwards [] with ω
    change Q ω=‖Real.sqrt (Q ω)‖^2
    rw [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (hQ0 ω)]
  have hb (t : ℝ≥0) (ω : Ω) : ‖X t ω‖≤D ω := by
    by_cases hω : MemLp (fun s => f (s,ω)) 2 (timeMeasure H)
    · simp only [X,if_pos hω]
      apply (sq_le_sq₀ (norm_nonneg _) (hD0 ω)).mp
      change ‖value H S (HeatControlAdapted.clamp U H) t ω‖^2≤(Real.sqrt (Q ω))^2
      rw [Real.sq_sqrt (hQ0 ω)]
      exact energy_pointwise H S hS hcontr f hf ω hω t
    · simp only [X,if_neg hω,norm_zero,hD0]
  have hXL2 : MemLp (Function.uncurry X) 2 (energyMeasure μ H) := by
    apply (hDm.comp_snd (timeMeasure H)).mono' (hXp.mono (predictable_le_product F)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => hb p.1 p.2)
  have hXtrim : @MemLp _ _ F.predictable _ _ (Function.uncurry X) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) :=
    (eLpNorm_trim (predictable_le_product F) hXp).trans_lt hXL2.eLpNorm_lt_top
  let A : Process (E := E) F μ H := hXtrim.toLp (Function.uncurry X)
  refine ⟨A,X,hXc,hXa,hXp,ae_eq_of_ae_eq_trim hXtrim.coeFn_toLp,hrep,D,hDm,hD0,hb,?_⟩
  exact HeatPathMaximum.integrable_square μ H X
    (fun t => (hXa t).measurable.mono (F.le t) le_rfl) hXc D hDm hD0 (fun t _ ω => hb t ω)

end HeatProgressiveControl
#check @HeatProgressiveControl.exists_version
#print axioms HeatProgressiveControl.exists_version
