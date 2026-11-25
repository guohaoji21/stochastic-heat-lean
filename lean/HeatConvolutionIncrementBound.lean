import HeatAgePowers
import HeatVolterraKernel
import SHEStochastic.ScalarLipschitzAgeDensity

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatConvolutionIncrementBound
open MeasureTheory SHE SHE.PredictableL2 HeatVolterraKernel
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (S : ℝ≥0 → E →L[ℝ] E) (hcontr : ∀ t x, ‖S t x‖≤‖x‖) (M : E →L[ℝ] E)
  (hsem : ∀ s t, S (s+t)=(S s).comp (S t))
  (hsmooth : ∀ τ δ : ℝ≥0, 0<τ → ∀ x : E,
    ‖S δ (S τ x)-S τ x‖≤((δ:ℝ)/(τ:ℝ))^(3/8:ℝ)*‖x‖)

include hcontr hsem hsmooth in
theorem old_bound (u : ℝ≥0 × Ω → E) {H s t r : ℝ≥0} (hr : r<s) (hst : s≤t) (ht : t≤H) (ω : Ω) :
    ‖raw S M u (t,(r,ω))-raw S M u (s,(r,ω))‖^2 ≤
      ((H:ℝ)^(1/2:ℝ)*‖M‖^2)*((t:ℝ)-(s:ℝ))^(1/4:ℝ)*
        ((s:ℝ)-(r:ℝ))^(-(3/4:ℝ))*‖u (r,ω)‖^2 := by
  rw [raw,raw,if_pos (hr.trans_le hst),if_pos hr]
  have he : S (t-r) (M (u (r,ω)))=S (t-s) (S (s-r) (M (u (r,ω)))) := by
    have hh := congrArg (fun A : E →L[ℝ] E => A (M (u (r,ω)))) (hsem (t-s) (s-r))
    rw [tsub_add_tsub_cancel hst hr.le] at hh
    exact hh
  rw [he]
  have hsm := hsmooth (s-r) (t-s) (tsub_pos_iff_lt.mpr hr) (M (u (r,ω)))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hsm 2
  have hup := pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm (u (r,ω))) 2
  rw [mul_pow] at hsq hup
  rw [NNReal.coe_sub hst,NNReal.coe_sub hr.le] at hsq
  have hδ : 0≤(t:ℝ)-(s:ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
  have hδH : (t:ℝ)-(s:ℝ)≤H := (sub_le_self _ s.property).trans (by exact_mod_cast ht)
  have hr0 : 0<(s:ℝ)-(r:ℝ) := sub_pos.mpr (by exact_mod_cast hr)
  have hp := HeatAgePowers.old hδ hδH hr0
  calc
    _ ≤ ((((t:ℝ)-(s:ℝ))/((s:ℝ)-(r:ℝ)))^(3/8:ℝ))^2*‖M (u (r,ω))‖^2 := hsq
    _ ≤ ((((t:ℝ)-(s:ℝ))/((s:ℝ)-(r:ℝ)))^(3/8:ℝ))^2*(‖M‖^2*‖u (r,ω)‖^2) :=
      mul_le_mul_of_nonneg_left hup (sq_nonneg _)
    _ ≤ ((H:ℝ)^(1/2:ℝ)*((t:ℝ)-(s:ℝ))^(1/4:ℝ)*((s:ℝ)-(r:ℝ))^(-(3/4:ℝ)))*
        (‖M‖^2*‖u (r,ω)‖^2) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by ring

include hcontr in
theorem fresh_bound (u : ℝ≥0 × Ω → E) {H s t r : ℝ≥0} (hsr : s≤r) (hr : r<t) (ht : t≤H) (ω : Ω) :
    ‖raw S M u (t,(r,ω))-raw S M u (s,(r,ω))‖^2 ≤
      ((H:ℝ)^(1/2:ℝ)*‖M‖^2)*((t:ℝ)-(r:ℝ))^(-(1/2:ℝ))*‖u (r,ω)‖^2 := by
  rw [raw,raw,if_pos hr,if_neg (not_lt.mpr hsr),sub_zero]
  have hn := pow_le_pow_left₀ (norm_nonneg _) ((hcontr (t-r) (M (u (r,ω)))).trans (M.le_opNorm (u (r,ω)))) 2
  rw [mul_pow] at hn
  have hp := HeatAgePowers.fresh (sub_pos.mpr (show (r:ℝ)<t from by exact_mod_cast hr))
    ((sub_le_self _ r.property).trans (show (t:ℝ)≤H from by exact_mod_cast ht))
  calc
    _ ≤ ‖M‖^2*‖u (r,ω)‖^2 := hn
    _ ≤ ((H:ℝ)^(1/2:ℝ)*((t:ℝ)-(r:ℝ))^(-(1/2:ℝ)))*(‖M‖^2*‖u (r,ω)‖^2) :=
      le_mul_of_one_le_left (by positivity) hp
    _ = _ := by ring

include hcontr hsem hsmooth in
theorem density_bound (u : ℝ≥0 × Ω → E) {H s t : ℝ≥0} (hst : s≤t) (ht : t≤H) (p : ℝ≥0 × Ω) :
    ENNReal.ofReal (‖raw S M u (t,p)-raw S M u (s,p)‖^2) ≤
      SHEStochastic.ScalarLipschitzAgeDensity.density ((H:ℝ)^(1/2:ℝ)*‖M‖^2) s t p.1 *
        ENNReal.ofReal (‖u p‖^2) := by
  have hδ : 0≤(t:ℝ)-(s:ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
  by_cases hr : p.1<s
  · have hr0 : 0<(s:ℝ)-(p.1:ℝ) := sub_pos.mpr (by exact_mod_cast hr)
    rw [SHEStochastic.ScalarLipschitzAgeDensity.density,if_pos hr,←ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (old_bound S hcontr M hsem hsmooth u hr hst ht p.2)
  · by_cases ht' : p.1<t
    · have hr0 : 0<(t:ℝ)-(p.1:ℝ) := sub_pos.mpr (by exact_mod_cast ht')
      rw [SHEStochastic.ScalarLipschitzAgeDensity.density,if_neg hr,if_pos ht',←ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (fresh_bound S hcontr M u (le_of_not_gt hr) ht' ht p.2)
    · simp only [raw,if_neg hr,if_neg ht',sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,zero_le]

end HeatConvolutionIncrementBound
#check @HeatConvolutionIncrementBound.old_bound
#print axioms HeatConvolutionIncrementBound.old_bound
#check @HeatConvolutionIncrementBound.fresh_bound
#print axioms HeatConvolutionIncrementBound.fresh_bound
#check @HeatConvolutionIncrementBound.density_bound
#print axioms HeatConvolutionIncrementBound.density_bound
