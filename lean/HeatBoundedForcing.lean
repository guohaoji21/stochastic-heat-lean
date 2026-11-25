import SHEStochastic.BallProjection
import HeatMomentBall
import SHE.ContinuousPredictable

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatBoundedForcing
open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem bounded_process (G : ℝ≥0 → Ω → E)
    (hp : StronglyMeasurable[F.predictable] (Function.uncurry G))
    (C : ℝ) (hC : 0≤C) (hb : ∀ t ω, ‖G t ω‖≤C) :
    ∃ A : Process (E := E) F μ H, A=ᵐ[energyMeasure μ H] Function.uncurry G ∧ A∈HeatMomentBall.Ball (C^16) := by
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure;infer_instance
  have hm : MemLp (Function.uncurry G) 2 (energyMeasure μ H) :=
    (memLp_const C).mono' (hp.mono (predictable_le_product F)).aestronglyMeasurable
      (Eventually.of_forall (fun p => hb p.1 p.2))
  have htrim : @MemLp _ _ F.predictable _ _ (Function.uncurry G) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) :=
    (eLpNorm_trim (predictable_le_product F) hp).trans_lt hm.eLpNorm_lt_top
  let A : Process (E := E) F μ H := htrim.toLp (Function.uncurry G)
  have hAE : A=ᵐ[energyMeasure μ H] Function.uncurry G := ae_eq_of_ae_eq_trim htrim.coeFn_toLp
  refine ⟨A,hAE,?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hAE] with t ht
  rw [HeatMomentBall.moment_congr ht]
  calc
    _ ≤ ∫⁻ _ω,ENNReal.ofReal (C^16) ∂μ := lintegral_mono (fun ω =>
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hb t ω) 16))
    _ = _ := by simp

end HeatBoundedForcing
#check @HeatBoundedForcing.bounded_process
#print HeatBoundedForcing.bounded_process
#print axioms HeatBoundedForcing.bounded_process
