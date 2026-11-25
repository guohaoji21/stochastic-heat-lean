import SHEStochastic.FiniteScalarIto

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace HeatRawItoCompatibility

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  (meas : ∀ t, Measurable (B t))
  (hF : ∀ t, MathFin.ItoIntegralL2.natFiltration meas t ≤ F t)

include hF in
private theorem predictable_le :
    (MathFin.ItoIntegralL2.natFiltration meas).predictable ≤ F.predictable := by
  rw [← MathFin.ItoIntegralCLM.generateFrom_predictableRect meas]
  apply MeasurableSpace.generateFrom_le
  rintro A (⟨S, hS, rfl⟩ | ⟨a, b, _, S, hS, rfl⟩)
  · exact measurableSet_predictable_singleton_bot_prod (𝓕 := F) (hF _ S hS)
  · exact measurableSet_predictable_Ioc_prod (𝓕 := F) a b (hF _ S hS)

local notation "ν" => SHEStochastic.FiniteScalarIto.inputMeasure F μ
local notation "νraw" => fun H => MathFin.ItoIntegralCLM.trimMeasure_T (μ := μ) H meas

private theorem trim_eq (H : ℝ≥0) : (ν H).trim (predictable_le meas hF) = νraw H :=
  trim_trim (hm₂ := F.predictable_le_prod)

include hF in
private theorem ae_of_raw (H : ℝ≥0) {f g : ℝ≥0 × Ω → ℝ} (he : f =ᵐ[νraw H] g) :
    f =ᵐ[ν H] g :=
  ae_eq_of_ae_eq_trim (hm := predictable_le meas hF) (by rwa [trim_eq meas hF H])

include hF in
private theorem memLp_embed (H : ℝ≥0) (u : Lp ℝ 2 (νraw H)) :
    MemLp (u : ℝ≥0 × Ω → ℝ) 2 (ν H) := by
  apply memLp_of_memLp_trim (μ := ν H) (predictable_le meas hF)
  rw [trim_eq meas hF H]
  exact Lp.memLp u

/-- Include raw predictable inputs in the larger predictable space with the
same probability measure and time cutoff. -/
def embed (H : ℝ≥0) : Lp ℝ 2 (νraw H) →ₗᵢ[ℝ] Lp ℝ 2 (ν H) where
  toFun u := (memLp_embed meas hF H u).toLp u
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(memLp_embed meas hF H (u + v)).coeFn_toLp,
      (memLp_embed meas hF H u).coeFn_toLp, (memLp_embed meas hF H v).coeFn_toLp,
      Lp.coeFn_add ((memLp_embed meas hF H u).toLp u) ((memLp_embed meas hF H v).toLp v),
      ae_of_raw meas hF H (Lp.coeFn_add u v)] with z hsum hu hv hs hz
    rw [hsum, hs]
    change (u + v) z = ((memLp_embed meas hF H u).toLp u) z + ((memLp_embed meas hF H v).toLp v) z
    rw [hu, hv]
    exact hz
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(memLp_embed meas hF H (c • u)).coeFn_toLp,
      (memLp_embed meas hF H u).coeFn_toLp, Lp.coeFn_smul c ((memLp_embed meas hF H u).toLp u),
      ae_of_raw meas hF H (Lp.coeFn_smul c u)] with z hsm hu hs hz
    rw [RingHom.id_apply, hsm, hs]
    change (c • u) z = c * ((memLp_embed meas hF H u).toLp u) z
    rw [hu]
    exact hz
  norm_map' u := by
    change ‖(memLp_embed meas hF H u).toLp u‖ = ‖u‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    calc
      _ = eLpNorm (u : ℝ≥0 × Ω → ℝ) 2 ((ν H).trim (predictable_le meas hF)) :=
        (eLpNorm_trim (predictable_le meas hF) (Lp.stronglyMeasurable u)).symm
      _ = _ := by rw [trim_eq (μ := μ) meas hF H]

private theorem embed_ae (H : ℝ≥0) (u : Lp ℝ 2 (νraw H)) : embed meas hF H u =ᵐ[ν H] u :=
  (memLp_embed meas hF H u).coeFn_toLp

private def simple (H : ℝ≥0) (v : MathFin.ItoIntegralCLM.TBoundedSP H meas) :
    SHEStochastic.FiniteScalarIto.Simple F H :=
  ⟨{ valueBot := v.val.valueBot
     value := v.val.value
     le_of_mem_support_value := v.val.le_of_mem_support_value
     measurable_valueBot := v.val.measurable_valueBot.mono (hF _) le_rfl
     measurable_value' := fun p _ => (v.val.measurable_value p).mono (hF _) le_rfl
     bounded_valueBot := v.val.bounded_valueBot
     bounded_value := v.val.bounded_value }, v.property⟩

private theorem embed_simple (H : ℝ≥0) (v : MathFin.ItoIntegralCLM.TBoundedSP H meas) :
    embed meas hF H (MathFin.ItoIntegralCLM.simpleAssembly_T (μ := μ) H meas v) =
      SHEStochastic.FiniteScalarIto.embedding F μ H (simple meas hF H v) := by
  let w := simple meas hF H v
  have hraw := (MathFin.ItoIntegralCLM.memLp_uncurry_trim_T (μ := μ) H meas v.val).coeFn_toLp
  have hw := (SHEStochastic.FilteredItoCLM.memLp_uncurry_trim_T (𝓖 := F) (μ := μ) H
    (B := fun _ _ => (0 : ℝ)) (fun _ => measurable_const) w.val).coeFn_toLp
  apply Lp.ext
  exact (embed_ae meas hF H _).trans ((ae_of_raw meas hF H hraw).trans hw.symm)

/-- The raw Itô integral agrees with the project's finite-horizon coordinate
integral on the embedded raw predictable inputs. -/
theorem integral (hB : IsPreBrownianReal B μ) (H : ℝ≥0)
    {ι : Type*} [DecidableEq ι] (Q : SHEStochastic.FiniteScalarIto.Coordinates F μ H ι)
    (i : ι) (hW : Q.W i = B) (u : Lp ℝ 2 (νraw H)) :
    SHEStochastic.FiniteScalarIto.rawIsometry Q i (embed meas hF H u) =
      MathFin.ItoIntegralCLM.itoIntegralCLM_T hB H meas u := by
  let A := (SHEStochastic.FiniteScalarIto.rawIsometry Q i).comp (embed meas hF H)
  let D := MathFin.ItoIntegralCLM.itoIntegralCLM_T hB H meas
  refine congrFun (DenseRange.equalizer
    (MathFin.ItoIntegralCLM.simpleAssembly_T_denseRange (μ := μ) H meas)
    A.continuous D.continuous (funext ?_)) u
  intro v
  change SHEStochastic.FiniteScalarIto.rawIsometry Q i
    (embed meas hF H (MathFin.ItoIntegralCLM.simpleAssembly_T H meas v)) =
      D (MathFin.ItoIntegralCLM.simpleAssembly_T H meas v)
  rw [embed_simple meas hF, SHEStochastic.FiniteScalarIto.rawIsometry_simple,
    show D = MathFin.ItoIntegralCLM.itoIntegralCLM_T hB H meas from rfl,
    MathFin.ItoIntegralCLM.itoIntegralCLM_T_simpleAssembly_T]
  apply Lp.ext
  filter_upwards [(SHEStochastic.FiniteScalarIto.memLp_simpleValue Q i
      (simple meas hF H v)).coeFn_toLp,
    (MathFin.ItoIntegralL2.memLp_itoSimple hB meas v.val).coeFn_toLp] with ω h1 h2
  change SHEStochastic.FiniteScalarIto.simpleLp Q i (simple meas hF H v) ω = _ at h1
  change MathFin.ItoIntegralL2.itoSimpleLp hB meas v.val ω = _ at h2
  rw [h2]
  rw [h1]
  simp only [SHEStochastic.FiniteScalarIto.simpleValue, SHEStochastic.FilteredItoL2.itoSimple,
    MathFin.ItoIntegralL2.itoSimple, simple, hW]

end HeatRawItoCompatibility

#print axioms HeatRawItoCompatibility.integral
