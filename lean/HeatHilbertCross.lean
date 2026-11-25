import HeatHilbertConditional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace HeatHilbertCross
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem conditional_polarization {m : MeasurableSpace Ω} (X Y : Lp E 2 μ)
    {A B C : Ω → ℝ}
    (hsum : μ[(fun ω => ‖(X + Y) ω‖ ^ 2) | m] =ᵐ[μ] μ[A | m])
    (hx : μ[(fun ω => ‖X ω‖ ^ 2) | m] =ᵐ[μ] μ[B | m])
    (hy : μ[(fun ω => ‖Y ω‖ ^ 2) | m] =ᵐ[μ] μ[C | m]) :
    μ[(fun ω => inner ℝ (X ω) (Y ω)) | m] =ᵐ[μ]
      fun ω => (μ[A | m] ω - μ[B | m] ω - μ[C | m] ω) / 2 := by
  let x : Ω → ℝ := fun ω => ‖X ω‖ ^ 2
  let y : Ω → ℝ := fun ω => ‖Y ω‖ ^ 2
  let z : Ω → ℝ := fun ω => inner ℝ (X ω) (Y ω)
  have hxint : Integrable x μ := (Lp.memLp X).norm.integrable_sq
  have hyint : Integrable y μ := (Lp.memLp Y).norm.integrable_sq
  have hzint : Integrable z μ := L2.integrable_inner X Y
  have hident : (fun ω => ‖(X + Y) ω‖ ^ 2) =ᵐ[μ] x + y + (2 : ℝ) • z := by
    filter_upwards [Lp.coeFn_add X Y] with ω hω
    simp only [hω, Pi.add_apply, Pi.smul_apply, smul_eq_mul, x, y, z]
    rw [norm_add_sq_real]
    ring
  have hlinear := condExp_add (hxint.add hyint) (hzint.const_mul 2) m
  have hlinear2 := condExp_add hxint hyint m
  have hscale := condExp_smul (μ := μ) (2 : ℝ) z m
  have hsum' := (condExp_congr_ae (m := m) hident).symm.trans hsum
  filter_upwards [hsum', hx, hy, hlinear, hlinear2, hscale] with ω hsumω hxω hyω hlinω hlin2ω hscaleω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hlinω hlin2ω hscaleω
  change μ[x + y + (2 : ℝ) • z | m] ω = μ[x + y | m] ω + μ[(2 : ℝ) • z | m] ω at hlinω
  change μ[x + y | m] ω = μ[x | m] ω + μ[y | m] ω at hlin2ω
  change μ[x + y + (2 : ℝ) • z | m] ω = μ[A | m] ω at hsumω
  change μ[x | m] ω = μ[B | m] ω at hxω
  change μ[y | m] ω = μ[C | m] ω at hyω
  change μ[z | m] ω = (μ[A | m] ω - μ[B | m] ω - μ[C | m] ω) / 2
  linarith

variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}

theorem bracket_polarization (u v : Process (E := C) F μ T) :
    ∀ᵐ ω ∂μ,
      (StochasticExponential.bracket F μ T (u + v) ω -
        StochasticExponential.bracket F μ T u ω -
        StochasticExponential.bracket F μ T v ω) / 2 =
      ∫ t, inner ℝ (u (t, ω)) (v (t, ω)) ∂timeMeasure T := by
  have hu := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)
  have hv := memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp v)
  have hinner : Integrable (fun p => inner ℝ (u p) (v p)) (energyMeasure μ T) := by
    refine (L2.integrable_inner (hu.toLp _) (hv.toLp _)).congr ?_
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with p hp hq
    rw [hp, hq]
  have hφ := hu.norm.integrable_sq.swap.prod_right_ae
  have hψ := hv.norm.integrable_sq.swap.prod_right_ae
  have hφψ := hinner.swap.prod_right_ae
  have hadd := ae_of_ae_trim (predictable_le_product F) (Lp.coeFn_add u v)
  have haddswap := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure T)).quasiMeasurePreserving.ae hadd
  have haddsec := Measure.ae_ae_of_ae_prod haddswap
  filter_upwards [hφ, hψ, hφψ, haddsec] with ω hφω hψω hφψω haddω
  change Integrable (fun t => ‖u (t, ω)‖ ^ 2) (timeMeasure T) at hφω
  change Integrable (fun t => ‖v (t, ω)‖ ^ 2) (timeMeasure T) at hψω
  change Integrable (fun t => inner ℝ (u (t, ω)) (v (t, ω))) (timeMeasure T) at hφψω
  have heq : (∫ t, ‖(u + v : Process (E := C) F μ T) (t, ω)‖ ^ 2 ∂timeMeasure T) =
      (∫ t, ‖u (t, ω)‖ ^ 2 ∂timeMeasure T) +
      2 * (∫ t, inner ℝ (u (t, ω)) (v (t, ω)) ∂timeMeasure T) +
      (∫ t, ‖v (t, ω)‖ ^ 2 ∂timeMeasure T) := by
    calc
      _ = ∫ t, (‖u (t, ω)‖ ^ 2 + 2 * inner ℝ (u (t, ω)) (v (t, ω)) +
          ‖v (t, ω)‖ ^ 2) ∂timeMeasure T := by
        apply integral_congr_ae
        filter_upwards [haddω] with t ht
        dsimp only [Prod.swap, Pi.add_apply] at ht
        rw [ht, norm_add_sq_real]
      _ = _ := by
        change (∫ t, ((fun t => ‖u (t, ω)‖ ^ 2) +
          (fun t => 2 * inner ℝ (u (t, ω)) (v (t, ω))) +
          (fun t => ‖v (t, ω)‖ ^ 2)) t ∂timeMeasure T) = _
        rw [integral_add' (hφω.add (hφψω.const_mul 2)) hψω,
          integral_add' hφω (hφψω.const_mul 2), integral_const_mul]
  simp only [StochasticExponential.bracket]
  linarith

theorem conditional_cross_polarized
    (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0)
    (u v : Process (E := C) F μ T) :
    μ[(fun ω => inner ℝ (J.integral (post F μ T a u) ω)
      (J.integral (post F μ T a v) ω)) | F a] =ᵐ[μ]
    fun ω => (μ[StochasticExponential.bracket F μ T (post F μ T a (u + v)) | F a] ω -
      μ[StochasticExponential.bracket F μ T (post F μ T a u) | F a] ω -
      μ[StochasticExponential.bracket F μ T (post F μ T a v) | F a] ω) / 2 := by
  apply conditional_polarization
  · simpa only [SHE.PastItoAlgebra.post_add, map_add] using
      HeatHilbertConditional.condExp_second J hlocal a (u + v)
  · exact HeatHilbertConditional.condExp_second J hlocal a u
  · exact HeatHilbertConditional.condExp_second J hlocal a v

theorem conditional_cross
    (J : StandardTerminalIto (C := C) (E := E) F μ T)
    (hlocal : StandardTerminalPastLocality J) (a : ℝ≥0)
    (u v : Process (E := C) F μ T) :
    μ[(fun ω => inner ℝ (J.integral (post F μ T a u) ω)
      (J.integral (post F μ T a v) ω)) | F a] =ᵐ[μ]
    μ[(fun ω => ∫ t, inner ℝ (post F μ T a u (t, ω))
      (post F μ T a v (t, ω)) ∂timeMeasure T) | F a] := by
  let A := StochasticExponential.bracket F μ T (post F μ T a (u + v))
  let B := StochasticExponential.bracket F μ T (post F μ T a u)
  let C := StochasticExponential.bracket F μ T (post F μ T a v)
  have hA : Integrable A μ := StochasticExponential.bracket_integrable F μ T _
  have hB : Integrable B μ := StochasticExponential.bracket_integrable F μ T _
  have hC : Integrable C μ := StochasticExponential.bracket_integrable F μ T _
  have hsub1 := condExp_sub hA hB (F a)
  have hsub2 := condExp_sub (hA.sub hB) hC (F a)
  have hscale := condExp_smul (μ := μ) (1 / 2 : ℝ) (A - B - C) (F a)
  have hpolar : μ[(fun ω => (A ω - B ω - C ω) / 2) | F a] =ᵐ[μ]
      fun ω => (μ[A | F a] ω - μ[B | F a] ω - μ[C | F a] ω) / 2 := by
    have hfun : (fun ω => (A ω - B ω - C ω) / 2) = (1 / 2 : ℝ) • (A - B - C) := by
      funext ω
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hfun]
    filter_upwards [hsub1, hsub2, hscale] with ω h1 h2 h3
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    linarith
  have hbracket := bracket_polarization (post F μ T a u) (post F μ T a v)
  rw [← SHE.PastItoAlgebra.post_add] at hbracket
  have heq := condExp_congr_ae (m := F a) hbracket
  have hcross := conditional_cross_polarized J hlocal a u v
  exact hcross.trans (hpolar.symm.trans heq)

end HeatHilbertCross

#check @HeatHilbertCross.conditional_cross
#print axioms HeatHilbertCross.conditional_cross
