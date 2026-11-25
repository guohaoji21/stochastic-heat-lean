import HeatVolterraSlice
import SHE.PredictableExponential
import HeatRegularMomentKernel

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatDampedSlice
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖) (M : E →L[ℝ] E)

def raw (γ : ℝ) (t : ℝ≥0) (u : Process (E := E) F μ H) (p : ℝ≥0 × Ω) : E :=
  if p.1<t then Real.exp (-γ*((t:ℝ)-(p.1:ℝ))) • S (t-p.1) (M (u p)) else 0

def input (γ : ℝ) (t : ℝ≥0) (u : Process (E := E) F μ H) : Process (E := E) F μ H :=
  Real.exp (-γ*(t:ℝ)) • HeatVolterraSlice.slice F μ H S hS hcontr M t (PredictableExponential.scale F μ H γ u)

include hS hcontr in
theorem input_ae (γ : ℝ) (t : ℝ≥0) (u : Process (E := E) F μ H) :
    input F μ H S hS hcontr M γ t u =ᵐ[energyMeasure μ H] raw F μ H S M γ t u := by
  have htime : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1≤H :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem H).mono fun s hs => hs.2)
  filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_smul (Real.exp (-γ*(t:ℝ)))
    (HeatVolterraSlice.slice F μ H S hS hcontr M t (PredictableExponential.scale F μ H γ u))),
    HeatVolterraSlice.slice_ae F μ H S hS hcontr M t (PredictableExponential.scale F μ H γ u),
    PredictableExponential.ae F μ H γ u,htime] with p hc hs hu htime
  change (Real.exp (-γ*(t:ℝ)) • HeatVolterraSlice.slice F μ H S hS hcontr M t
    (PredictableExponential.scale F μ H γ u)) p = _
  rw [hc]
  simp only [Pi.smul_apply,hs,HeatVolterraKernel.raw,raw]
  by_cases hp : p.1<t
  · rw [if_pos hp,if_pos hp,hu]
    simp only [PredictableExponential.weight,min_eq_left (show (p.1:ℝ)≤H from by exact_mod_cast htime),map_smul,smul_smul]
    rw [←Real.exp_add]
    congr 2
    ring
  · simp only [if_neg hp,smul_zero]

include hcontr in
theorem raw_bound (γ : ℝ) (t : ℝ≥0) (u : Process (E := E) F μ H) (p : ℝ≥0 × Ω) :
    ENNReal.ofReal (‖raw F μ H S M γ t u p‖^2) ≤
      ENNReal.ofReal (‖M‖^2) * HeatRegularKernel.kernel γ ((t:ℝ)-(p.1:ℝ)) *
        ENNReal.ofReal (‖u p‖^2) := by
  by_cases hp : p.1<t
  · have hd : 0<(t:ℝ)-(p.1:ℝ) := sub_pos.mpr (by exact_mod_cast hp)
    rw [raw,if_pos hp,HeatRegularKernel.kernel,Set.indicator_of_mem (show (t:ℝ)-(p.1:ℝ)∈Ioi (0:ℝ) from hd)]
    have hn := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg M) (norm_nonneg (u p)))).mpr
      ((hcontr (t-p.1) (M (u p))).trans (M.le_opNorm (u p)))
    have he : ‖Real.exp (-γ*((t:ℝ)-(p.1:ℝ)))‖^2 = Real.exp (-2*γ*((t:ℝ)-(p.1:ℝ))) := by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),pow_two,←Real.exp_add]
      congr 1
      ring
    rw [norm_smul,mul_pow,he,←ENNReal.ofReal_mul (sq_nonneg ‖M‖),
      ←ENNReal.ofReal_mul (mul_nonneg (sq_nonneg ‖M‖) (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left hn (Real.exp_pos (-2*γ*((t:ℝ)-(p.1:ℝ)))).le
    nlinarith only [hh]
  · simp only [raw,if_neg hp,norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,zero_le]

end HeatDampedSlice
#check @HeatDampedSlice.input_ae
#print axioms HeatDampedSlice.input_ae
#check @HeatDampedSlice.raw_bound
#print axioms HeatDampedSlice.raw_bound
