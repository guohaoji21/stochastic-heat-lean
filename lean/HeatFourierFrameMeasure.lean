import HeatFourierFrame
import HeatHilbertRandomStop
import SHE.LpEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatFourierFrameMeasure
open MeasureTheory Filter SHE SHE.PredictableL2 HeatIntervalNormalization HeatPhysicalGenerator
open HeatFourierFrame CircleHeat DyadicApproximation FiniteHaar AddCircle
open scoped NNReal ENNReal
local instance : MeasurableSpace Base := borel Base
local instance : BorelSpace Base := ⟨rfl⟩
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

theorem square_coefficient (x : Base) (n : ℤ) :
    (coordinate n x)^2=‖coefficient x n‖^2 := by
  rw [coordinate_coefficient,Complex.sq_norm]
  have hr := HeatOddFourier.odd_coefficient_re_zero (paperOddEquiv x) n
  change (coefficient x n).re=0 at hr
  simp [Complex.normSq_apply,hr,pow_two]

theorem summable (x : Base) : Summable (fun n : ℤ => (coordinate n x)^2) := by
  have hs := CircleHeat.summable_fourier_sq (realEmbed (paperOddEquiv x : RealL2))
  apply hs.congr
  intro n
  exact (square_coefficient x n).symm

theorem parseval_ennreal (x : Base) :
    (∑' n : ℤ,ENNReal.ofReal ((coordinate n x)^2))=ENNReal.ofReal (‖x‖^2) := by
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) (summable x),←parseval]

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

theorem integrated_parseval (f : X → Base) (hf : Measurable f) :
    (∑' n : ℤ,∫⁻ x,ENNReal.ofReal ((coordinate n (f x))^2) ∂ν)=
      ∫⁻ x,ENNReal.ofReal (‖f x‖^2) ∂ν := by
  have hm (n : ℤ) : AEMeasurable (fun x => ENNReal.ofReal ((coordinate n (f x))^2)) ν :=
    (((coordinate n).continuous.measurable.comp hf).pow_const 2).ennreal_ofReal.aemeasurable
  calc
    _ = ∫⁻ x,∑' n : ℤ,ENNReal.ofReal ((coordinate n (f x))^2) ∂ν := (lintegral_tsum hm).symm
    _ = _ := lintegral_congr (fun x => parseval_ennreal (f x))

theorem lp_parseval (u : Lp Base 2 ν) :
    (∑' n : ℤ,ENNReal.ofReal (‖((coordinate n).compLpL 2 ν) u‖^2))=ENNReal.ofReal (‖u‖^2) := by
  calc
    _ = ∑' n : ℤ,∫⁻ x,ENNReal.ofReal ((coordinate n (u x))^2) ∂ν := by
      apply tsum_congr
      intro n
      rw [SHE.LpEnergy.lintegral_energy]
      apply lintegral_congr_ae
      filter_upwards [(coordinate n).coeFn_compLpL u] with x hx
      rw [hx,Real.norm_eq_abs,sq_abs]
    _ = _ := by rw [integrated_parseval ν u (Lp.stronglyMeasurable u).measurable,←SHE.LpEnergy.lintegral_energy]

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem projected_parseval (u : Process (E := Base) F μ H) :
    (∑' n : ℤ,ENNReal.ofReal (‖HeatHilbertRandomStop.project F μ H (coordinate n) u‖^2))=
      ENNReal.ofReal (‖u‖^2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have he (n : ℤ) : ‖HeatHilbertRandomStop.project F μ H (coordinate n) u‖=
      ‖((coordinate n).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product F))) u‖ :=
    (HeatUnitHilbertLp.lpEquiv _).norm_map _
  simp_rw [he]
  exact lp_parseval ((energyMeasure μ H).trim (predictable_le_product F)) u

end HeatFourierFrameMeasure
#check @HeatFourierFrameMeasure.square_coefficient
#print axioms HeatFourierFrameMeasure.square_coefficient
#check @HeatFourierFrameMeasure.summable
#print axioms HeatFourierFrameMeasure.summable
#check @HeatFourierFrameMeasure.parseval_ennreal
#print axioms HeatFourierFrameMeasure.parseval_ennreal
#check @HeatFourierFrameMeasure.integrated_parseval
#print axioms HeatFourierFrameMeasure.integrated_parseval
#check @HeatFourierFrameMeasure.lp_parseval
#print axioms HeatFourierFrameMeasure.lp_parseval
#check @HeatFourierFrameMeasure.projected_parseval
#print HeatFourierFrameMeasure.projected_parseval
#print axioms HeatFourierFrameMeasure.projected_parseval
