import HeatHilbertRandomStop
import SHEStochastic.DoobL2Envelope
import SHEStochastic.ConditionalBracket
import SHE.LpEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatScalarMartingaleEnvelope
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem exists_envelope (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (hversions : SHEStochastic.ContinuousStoppedVersions J)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (u : Process (E := C) F μ H) :
    ∃ (X : ℝ≥0 → Ω → ℝ) (D : Ω → ℝ),
      (∀ ω, Continuous (X · ω)) ∧ StronglyAdapted F X ∧
      (∀ t, X t=ᵐ[μ] J.integral (stop F μ H t u)) ∧
      MemLp D 2 μ ∧ (∀ ω,0≤D ω) ∧
      (∀ t, t≤H → ∀ ω, |X t ω|≤D ω) ∧
      (∫ ω,(D ω)^2 ∂μ)≤4*‖u‖^2 := by
  obtain ⟨X,hc,hr0⟩ := hversions u
  have hr : ∀ t : ℝ≥0, X t=ᵐ[μ] J.integral (stop F μ H t u) := hr0
  have ha : StronglyAdapted F X := by
    apply NullCompleteFiltration.stronglyAdapted_of_versions F μ hnull
    intro t
    obtain ⟨Z,hZ,he⟩ := stopped_integral_adapted F μ H J t u
    exact ⟨Z,hZ,(hr t).trans he⟩
  have hm : Martingale X F μ := SHEStochastic.ConditionalBracket.martingale J hlocal u ha hr
  have hT : MemLp (X H) 2 μ := (Lp.memLp (J.integral (stop F μ H H u))).ae_eq (hr H).symm
  obtain ⟨D,hD,hDn,hbound,hmax⟩ := SHEStochastic.DoobL2Envelope.exists_envelope hm hc H hT
  refine ⟨X,D,hc,ha,hr,hD,hDn,?_,?_⟩
  · simpa only [Real.norm_eq_abs] using hbound
  have hp := SHEStochastic.DoobL2Envelope.power_bound hm hc H D hbound hmax 1
    (fun t => by simpa only [pow_one] using (hm.integrable t).norm)
    (by simpa only [pow_one] using hT.norm)
  norm_num only [Nat.mul_one] at hp
  have he : (∫⁻ ω,ENNReal.ofReal (‖X H ω‖^2) ∂μ)=ENNReal.ofReal (‖stop F μ H H u‖^2) := by
    calc
      _ = ∫⁻ ω,ENNReal.ofReal (‖J.integral (stop F μ H H u) ω‖^2) ∂μ :=
        lintegral_congr_ae ((hr H).fun_comp (fun r : ℝ => ENNReal.ofReal (‖r‖^2)))
      _ = _ := by rw [←SHE.LpEnergy.lintegral_energy,J.integral.norm_map]
  rw [he,←ofReal_integral_eq_lintegral_ofReal hD.integrable_sq
    (Eventually.of_forall (fun _ => sq_nonneg _)),←ENNReal.ofReal_ofNat (n := 4),
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)] at hp
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤4*‖stop F μ H H u‖^2)).mp hp
  have hn := StoppedInputResolvent.stop_norm_le F μ H u H
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]

end HeatScalarMartingaleEnvelope
#check @HeatScalarMartingaleEnvelope.exists_envelope
#print HeatScalarMartingaleEnvelope.exists_envelope
#print axioms HeatScalarMartingaleEnvelope.exists_envelope
