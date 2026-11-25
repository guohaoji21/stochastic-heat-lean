import HeatFourierFrameMeasure
import HeatPathMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace HeatModalEnergySummation
open MeasureTheory Filter HeatIntervalNormalization HeatFourierFrame
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem integrable_maximum (X : ℝ≥0 → Ω → Base) (hX : ∀ ω, Continuous (X · ω))
    (hXm : ∀ t,Measurable (X t)) (g : Base) (C D : ℤ → Ω → ℝ)
    (hC : ∀ n,MemLp (C n) 2 μ) (hD : ∀ n,MemLp (D n) 2 μ)
    (hCf : (∑' n : ℤ,∫⁻ ω,ENNReal.ofReal ((C n ω)^2) ∂μ)<∞)
    (hDf : (∑' n : ℤ,∫⁻ ω,ENNReal.ofReal ((D n ω)^2) ∂μ)<∞)
    (hb : ∀ n : ℤ, ∀ᵐ ω ∂μ, ∀ t, t≤H → |coordinate n (X t ω)|≤2*(|coordinate n g|+C n ω+D n ω)) :
    Integrable (fun ω => HeatPathMaximum.value H X ω^2) μ := by
  let B (n : ℤ) (ω : Ω) : ℝ≥0∞ := 12*(ENNReal.ofReal ((coordinate n g)^2)+
    ENNReal.ofReal ((C n ω)^2)+ENNReal.ofReal ((D n ω)^2))
  have hBm (n : ℤ) : AEMeasurable (B n) μ :=
    aemeasurable_const.mul ((aemeasurable_const.add ((hC n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal).add
      ((hD n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
  have hdom : ∀ᵐ ω ∂μ, ENNReal.ofReal (HeatPathMaximum.value H X ω^2)≤∑' n : ℤ,B n ω := by
    filter_upwards [ae_all_iff.mpr hb] with ω hω
    obtain ⟨t,ht,hmax⟩ := HeatPathMaximum.attained H X hX ω
    rw [hmax,←HeatFourierFrameMeasure.parseval_ennreal]
    apply ENNReal.tsum_le_tsum
    intro n
    have hs := hω n t ht
    have hreal : (coordinate n (X t ω))^2≤12*((coordinate n g)^2+(C n ω)^2+(D n ω)^2) := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hs 2
      rw [sq_abs] at hsq
      nlinarith [sq_abs (coordinate n g),sq_nonneg (|coordinate n g|-C n ω),
        sq_nonneg (|coordinate n g|-D n ω),sq_nonneg (C n ω-D n ω)]
    have he := ENNReal.ofReal_le_ofReal hreal
    simpa only [B,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤12),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] using he
  have hBi (n : ℤ) : (∫⁻ ω,B n ω ∂μ)=12*(ENNReal.ofReal ((coordinate n g)^2)+
      (∫⁻ ω,ENNReal.ofReal ((C n ω)^2) ∂μ)+(∫⁻ ω,ENNReal.ofReal ((D n ω)^2) ∂μ)) := by
    have hs : AEMeasurable (fun ω => ENNReal.ofReal ((coordinate n g)^2)+ENNReal.ofReal ((C n ω)^2)) μ :=
      aemeasurable_const.add ((hC n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
    unfold B
    rw [lintegral_const_mul' _ _ (by norm_num),lintegral_add_left' hs,
      lintegral_add_left' aemeasurable_const,lintegral_const]
    simp only [measure_univ,mul_one]
  have hfinite : (∫⁻ ω,∑' n : ℤ,B n ω ∂μ)<∞ := by
    rw [lintegral_tsum hBm]
    simp_rw [hBi]
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_add,ENNReal.tsum_add,
      HeatFourierFrameMeasure.parseval_ennreal]
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hCf⟩,hDf⟩)
  have hi : (∫⁻ ω,ENNReal.ofReal (HeatPathMaximum.value H X ω^2) ∂μ)<∞ :=
    (lintegral_mono_ae hdom).trans_lt hfinite
  refine ⟨((HeatPathMaximum.measurable H X hXm hX).pow_const 2).stronglyMeasurable.aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr hi

end HeatModalEnergySummation
#check @HeatModalEnergySummation.integrable_maximum
#print HeatModalEnergySummation.integrable_maximum
#print axioms HeatModalEnergySummation.integrable_maximum
