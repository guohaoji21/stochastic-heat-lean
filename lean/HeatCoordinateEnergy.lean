import HeatScalarControlBound
import HeatPathMaximum
import SHE.LpEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace HeatCoordinateEnergy

open MeasureTheory Filter SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {α E : Type*} [Countable α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (coordinate : α → E →L[ℝ] ℝ)
  (parseval : ∀ x, (∑' n, ENNReal.ofReal ((coordinate n x)^2)) = ENNReal.ofReal (‖x‖^2))

include parseval in
theorem integrated_parseval {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (f : X → E) (hf : Measurable f) :
    (∑' n, ∫⁻ x, ENNReal.ofReal ((coordinate n (f x))^2) ∂ν) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂ν := by
  have hm (n : α) : AEMeasurable (fun x => ENNReal.ofReal ((coordinate n (f x))^2)) ν :=
    (((coordinate n).continuous.measurable.comp hf).pow_const 2).ennreal_ofReal.aemeasurable
  rw [← lintegral_tsum hm]
  exact lintegral_congr (fun x => parseval (f x))

include parseval in
theorem lp_parseval {X : Type*} [MeasurableSpace X] (ν : Measure X) (u : Lp E 2 ν) :
    (∑' n, ENNReal.ofReal (‖((coordinate n).compLpL 2 ν) u‖^2)) = ENNReal.ofReal (‖u‖^2) := by
  calc
    _ = ∑' n, ∫⁻ x, ENNReal.ofReal ((coordinate n (u x))^2) ∂ν := by
      apply tsum_congr
      intro n
      rw [SHE.LpEnergy.lintegral_energy]
      apply lintegral_congr_ae
      filter_upwards [(coordinate n).coeFn_compLpL u] with x hx
      rw [hx, Real.norm_eq_abs, sq_abs]
    _ = _ := by rw [integrated_parseval coordinate parseval ν u (Lp.stronglyMeasurable u).measurable,
      ← SHE.LpEnergy.lintegral_energy]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

section Control
variable (f : ℝ≥0 × Ω → E) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))

def bound (n : α) : Ω → ℝ := HeatScalarControlBound.bound H (fun p => coordinate n (f p))

include hfm in
theorem square_integrable (n : α) : MemLp (bound coordinate H f n) 2 μ :=
  HeatScalarControlBound.square_integrable μ H _ ((coordinate n).comp_memLp' hfm)

include parseval hf hfm in
theorem energy :
    (∑' n : α,∫⁻ ω,ENNReal.ofReal ((bound coordinate H f n ω)^2) ∂μ)=
      ENNReal.ofReal (H:ℝ)*(∫⁻ p,ENNReal.ofReal (‖f p‖^2) ∂energyMeasure μ H) := by
  have he (n : α) : (∫⁻ ω,ENNReal.ofReal ((bound coordinate H f n ω)^2) ∂μ)=
      ENNReal.ofReal (H:ℝ)*(∫⁻ p,ENNReal.ofReal ((coordinate n (f p))^2) ∂energyMeasure μ H) := by
    have hm : MemLp (fun p => coordinate n (f p)) 2 (energyMeasure μ H) := by
      simpa only [Function.comp_def] using (coordinate n).comp_memLp' hfm
    have hi : Integrable (fun p => (coordinate n (f p))^2) (energyMeasure μ H) := by
      simpa only [Real.norm_eq_abs,sq_abs] using hm.norm.integrable_sq
    rw [←ofReal_integral_eq_lintegral_ofReal (square_integrable coordinate μ H f hfm n).integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _))]
    change ENNReal.ofReal (∫ ω,(HeatScalarControlBound.bound H (fun p => coordinate n (f p)) ω)^2 ∂μ)=_
    rw [HeatScalarControlBound.energy μ H _ hm]
    calc
      _ = ENNReal.ofReal (H:ℝ)*ENNReal.ofReal (∫ p,(coordinate n (f p))^2 ∂energyMeasure μ H) :=
        ENNReal.ofReal_mul H.property
      _ = _ := congrArg (fun z => ENNReal.ofReal (H:ℝ)*z)
        (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)))
  simp_rw [he]
  rw [ENNReal.tsum_mul_left,integrated_parseval coordinate parseval (energyMeasure μ H) f hf]

include parseval hf hfm in
theorem finite : (∑' n : α,∫⁻ ω,ENNReal.ofReal ((bound coordinate H f n ω)^2) ∂μ)<∞ := by
  rw [energy coordinate parseval μ H f hf hfm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mp hfm.norm.integrable_sq.2)

end Control

include parseval in
theorem integrable_maximum (X : ℝ≥0 → Ω → E) (hX : ∀ ω, Continuous (X · ω))
    (hXm : ∀ t,Measurable (X t)) (g : E) (C D : α → Ω → ℝ)
    (hC : ∀ n,MemLp (C n) 2 μ) (hD : ∀ n,MemLp (D n) 2 μ)
    (hCf : (∑' n : α,∫⁻ ω,ENNReal.ofReal ((C n ω)^2) ∂μ)<∞)
    (hDf : (∑' n : α,∫⁻ ω,ENNReal.ofReal ((D n ω)^2) ∂μ)<∞)
    (hb : ∀ n : α, ∀ᵐ ω ∂μ, ∀ t, t≤H → |coordinate n (X t ω)|≤2*(|coordinate n g|+C n ω+D n ω)) :
    Integrable (fun ω => HeatPathMaximum.value H X ω^2) μ := by
  let B (n : α) (ω : Ω) : ℝ≥0∞ := 12*(ENNReal.ofReal ((coordinate n g)^2)+
    ENNReal.ofReal ((C n ω)^2)+ENNReal.ofReal ((D n ω)^2))
  have hBm (n : α) : AEMeasurable (B n) μ :=
    aemeasurable_const.mul ((aemeasurable_const.add ((hC n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal).add
      ((hD n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
  have hdom : ∀ᵐ ω ∂μ, ENNReal.ofReal (HeatPathMaximum.value H X ω^2)≤∑' n : α,B n ω := by
    filter_upwards [ae_all_iff.mpr hb] with ω hω
    obtain ⟨t,ht,hmax⟩ := HeatPathMaximum.attained H X hX ω
    rw [hmax,←parseval]
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
  have hBi (n : α) : (∫⁻ ω,B n ω ∂μ)=12*(ENNReal.ofReal ((coordinate n g)^2)+
      (∫⁻ ω,ENNReal.ofReal ((C n ω)^2) ∂μ)+(∫⁻ ω,ENNReal.ofReal ((D n ω)^2) ∂μ)) := by
    have hs : AEMeasurable (fun ω => ENNReal.ofReal ((coordinate n g)^2)+ENNReal.ofReal ((C n ω)^2)) μ :=
      aemeasurable_const.add ((hC n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
    unfold B
    rw [lintegral_const_mul' _ _ (by norm_num),lintegral_add_left' hs,
      lintegral_add_left' aemeasurable_const,lintegral_const]
    simp only [measure_univ,mul_one]
  have hfinite : (∫⁻ ω,∑' n : α,B n ω ∂μ)<∞ := by
    rw [lintegral_tsum hBm]
    simp_rw [hBi]
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_add,ENNReal.tsum_add,
      parseval]
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hCf⟩,hDf⟩)
  have hi : (∫⁻ ω,ENNReal.ofReal (HeatPathMaximum.value H X ω^2) ∂μ)<∞ :=
    (lintegral_mono_ae hdom).trans_lt hfinite
  refine ⟨((HeatPathMaximum.measurable H X hXm hX).pow_const 2).stronglyMeasurable.aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr hi

end HeatCoordinateEnergy

#print axioms HeatCoordinateEnergy.integrable_maximum
#print axioms HeatCoordinateEnergy.lp_parseval
