import HeatScalarDampingNNReal
import HeatControlConvolution
import HeatTimeRestriction

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatScalarControlBound
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (f : ℝ≥0 × Ω → ℝ) (hf : Measurable f) (hfm : MemLp f 2 (energyMeasure μ H))

def bound (ω : Ω) : ℝ := Real.sqrt ((H:ℝ)*(∫ s,(f (s,ω))^2 ∂timeMeasure H))

theorem nonnegative (ω : Ω) : 0≤bound H f ω := Real.sqrt_nonneg _

include hfm in
theorem square_integrable : MemLp (bound H f) 2 μ := by
  have hi := hfm.norm.integrable_sq.integral_prod_right.const_mul (H:ℝ)
  apply (memLp_two_iff_integrable_sq_norm
    (Real.continuous_sqrt.comp_aestronglyMeasurable (by simpa only [Real.norm_eq_abs,sq_abs] using hi.aestronglyMeasurable))).mpr
  apply hi.congr
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity : 0≤(H:ℝ)*(∫ s,(f (s,ω))^2 ∂timeMeasure H))]
  simp only [Real.norm_eq_abs,sq_abs]

include hfm in
theorem energy : (∫ ω,(bound H f ω)^2 ∂μ)=(H:ℝ)*(∫ p,(f p)^2 ∂energyMeasure μ H) := by
  unfold bound
  simp_rw [Real.sq_sqrt (by positivity : 0≤(H:ℝ)*(∫ s,(f (s,_))^2 ∂timeMeasure H))]
  rw [integral_const_mul]
  congr 1
  have hi : Integrable (fun p => (f p)^2) (energyMeasure μ H) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hfm.norm.integrable_sq
  exact (integral_prod_symm _ hi).symm

include hf hfm in
theorem integral_bound (t : ℝ≥0) (ht : t≤H) :
    ∀ᵐ ω ∂μ, |∫ s,f (s,ω) ∂timeMeasure t|≤bound H f ω := by
  filter_upwards [HeatControlConvolution.time_memLp μ H f hf hfm] with ω hω
  have hm := hω.mono_measure (HeatTimeRestriction.mono ht)
  have he := IntegralEnergy.norm_integral_sq (timeMeasure t) (fun s => f (s,ω)) hm
  have hmass : (timeMeasure t).real univ=(t:ℝ) := by
    rw [Measure.real,timeMeasure_mass]
    exact ENNReal.toReal_ofReal t.property
  rw [hmass] at he
  have hi : Integrable (fun s => (f (s,ω))^2) (timeMeasure H) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hω.norm.integrable_sq
  have hmono : (∫ s,(f (s,ω))^2 ∂timeMeasure t)≤∫ s,(f (s,ω))^2 ∂timeMeasure H :=
    integral_mono_measure (HeatTimeRestriction.mono ht) (Eventually.of_forall (fun _ => sq_nonneg _)) hi
  have hle : (t:ℝ)≤(H:ℝ) := by exact_mod_cast ht
  have hn : 0≤∫ s,(f (s,ω))^2 ∂timeMeasure H := integral_nonneg (fun _ => sq_nonneg _)
  change |∫ s,f (s,ω) ∂timeMeasure t|≤Real.sqrt ((H:ℝ)*∫ s,(f (s,ω))^2 ∂timeMeasure H)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs]
  simp only [Real.norm_eq_abs,sq_abs] at he
  exact (he.trans ((mul_le_mul_of_nonneg_left hmono t.property).trans
    (mul_le_mul_of_nonneg_right hle hn))).trans_eq (Real.sq_sqrt (mul_nonneg H.property hn)).symm

end HeatScalarControlBound
#check @HeatScalarControlBound.nonnegative
#print axioms HeatScalarControlBound.nonnegative
#check @HeatScalarControlBound.square_integrable
#print axioms HeatScalarControlBound.square_integrable
#check @HeatScalarControlBound.energy
#print axioms HeatScalarControlBound.energy
#check @HeatScalarControlBound.integral_bound
#print HeatScalarControlBound.integral_bound
#print axioms HeatScalarControlBound.integral_bound
