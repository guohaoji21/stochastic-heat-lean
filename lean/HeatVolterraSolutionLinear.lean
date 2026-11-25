import HeatVolterraUniformEnergy
import HeatSliceNorm
import HeatPredictableObservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace HeatVolterraSolutionLinear

open Filter MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (S : ℝ≥0 → E →L[ℝ] E) (hS : ∀ x, Continuous (fun t => S t x))
  (hcontr : ∀ t x, ‖S t x‖ ≤ ‖x‖)

local notation "Proc" => Process (E := E) F μ H

omit [CompleteSpace E] in
include hS hcontr in
private theorem orbit_add (x y : E) :
    HeatVolterraForcing.orbit F μ H S hS hcontr (x + y) =
      HeatVolterraForcing.orbit F μ H S hS hcontr x + HeatVolterraForcing.orbit F μ H S hS hcontr y := by
  let o := HeatVolterraForcing.orbit F μ H S hS hcontr
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [HeatVolterraForcing.orbit_ae F μ H S hS hcontr (x + y),
    HeatVolterraForcing.orbit_ae F μ H S hS hcontr x, HeatVolterraForcing.orbit_ae F μ H S hS hcontr y,
    ae_eq_of_ae_eq_trim (Lp.coeFn_add (o x) (o y))] with p hxy hx hy h
  rw [hxy, h, Pi.add_apply, hx, hy, map_add]

omit [CompleteSpace E] in
include hS hcontr in
private theorem orbit_smul (c : ℝ) (x : E) :
    HeatVolterraForcing.orbit F μ H S hS hcontr (c • x) =
      c • HeatVolterraForcing.orbit F μ H S hS hcontr x := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [HeatVolterraForcing.orbit_ae F μ H S hS hcontr (c • x),
    HeatVolterraForcing.orbit_ae F μ H S hS hcontr x,
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul c (HeatVolterraForcing.orbit F μ H S hS hcontr x))]
    with p hc hx h
  rw [hc, h, Pi.smul_apply, hx, map_smul]

def orbit : E →L[ℝ] Proc :=
  (show E →ₗ[ℝ] Proc from
    { toFun := HeatVolterraForcing.orbit F μ H S hS hcontr
      map_add' := orbit_add F μ H S hS hcontr
      map_smul' := orbit_smul F μ H S hS hcontr }).mkContinuous (Real.sqrt (H : ℝ)) fun x => by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    have hs : (Real.sqrt (H : ℝ)) ^ 2 = (H : ℝ) := Real.sq_sqrt H.property
    rw [mul_pow, hs]
    exact HeatVolterraUniformEnergy.orbit_energy F μ H S hS hcontr x

variable (M : E →L[ℝ] E)

local notation "slice" => HeatVolterraSlice.slice F μ H S hS hcontr M

include hS hcontr in
private theorem slice_add (t : ℝ≥0) (u v : Proc) : slice t (u + v) = slice t u + slice t v := by
  have h := HeatConvolutionAlgebra.slice_sub F μ H S hS hcontr M (u + v) v t
  rw [add_sub_cancel_right] at h
  exact sub_eq_iff_eq_add.mp h.symm

omit [CompleteSpace E] in
include hS hcontr in
private theorem slice_smul (t : ℝ≥0) (c : ℝ) (u : Proc) : slice t (c • u) = c • slice t u := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [HeatVolterraSlice.slice_ae F μ H S hS hcontr M t (c • u),
    HeatVolterraSlice.slice_ae F μ H S hS hcontr M t u,
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul c u), ae_eq_of_ae_eq_trim (Lp.coeFn_smul c (slice t u))]
    with p hc hu hcu hcs
  rw [hc, hcs, Pi.smul_apply, hu]
  unfold HeatVolterraKernel.raw
  split_ifs
  · rw [hcu, Pi.smul_apply, map_smul, map_smul]
  · exact (smul_zero c).symm

/-- The predictable integrand of the mild convolution at a fixed time. -/
def sliceOperator (t : ℝ≥0) : Proc →L[ℝ] Proc :=
  (show Proc →ₗ[ℝ] Proc from
    { toFun := slice t
      map_add' := slice_add F μ H S hS hcontr M t
      map_smul' := slice_smul F μ H S hS hcontr M t }).mkContinuous ‖M‖
    (fun u => HeatSliceNorm.bound F μ H S hS hcontr M u t)

variable (hsem : ∀ s t, S (s + t) = (S s).comp (S t))
  (I : StandardTerminalIto (C := E) (E := E) F μ H)

local notation "N" => HeatVolterraFixedPoint.convolution F μ H S hS hcontr M hsem I

include hS hcontr in
private theorem convolution_add (u v : Proc) : N (u + v) = N u + N v := by
  have h := HeatConvolutionAlgebra.sub F μ H S hS hcontr M hsem I (u + v) v
  rw [add_sub_cancel_right] at h
  exact sub_eq_iff_eq_add.mp h.symm

include hS hcontr in
private theorem convolution_smul (c : ℝ) (u : Proc) : N (c • u) = c • N u := by
  apply HeatPredictableObservation.eq_of_slices F μ H
  filter_upwards [HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem (c • u),
    HeatVolterraContinuity.convolution_slices F μ H S hS hcontr M I hsem u,
    Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_smul c (N u)))] with t hc hu hsm
  rw [slice_smul F μ H S hS hcontr M t c u, map_smul] at hc
  filter_upwards [hc, hu, hsm, Lp.coeFn_smul c (I.integral (slice t u))] with ω hc hu hsm hi
  change N (c • u) (t, ω) = _ at hc
  change N u (t, ω) = _ at hu
  rw [hc, hsm, hi, Pi.smul_apply, Pi.smul_apply, hu]

private def fixedPoint (f : Proc) : Proc :=
  Classical.choose (HeatVolterraFixedPoint.exists_unique F μ H S hS hcontr M hsem I f)

include hS hcontr in
private theorem fixedPoint_equation (f : Proc) :
    fixedPoint F μ H S hS hcontr M hsem I f = f + N (fixedPoint F μ H S hS hcontr M hsem I f) :=
  (Classical.choose_spec (HeatVolterraFixedPoint.exists_unique F μ H S hS hcontr M hsem I f)).1

include hS hcontr in
private theorem fixedPoint_unique (f u : Proc) (hu : u = f + N u) :
    u = fixedPoint F μ H S hS hcontr M hsem I f :=
  (Classical.choose_spec (HeatVolterraFixedPoint.exists_unique F μ H S hS hcontr M hsem I f)).2 u hu

/-- The solution of the predictable stochastic Volterra equation depends
continuously and linearly on its forcing. -/
def solve : Proc →L[ℝ] Proc := by
  let v := fixedPoint F μ H S hS hcontr M hsem I
  let lin : Proc →ₗ[ℝ] Proc :=
    { toFun := v
      map_add' := fun f g => by
        symm
        apply fixedPoint_unique F μ H S hS hcontr M hsem I
        calc
          v f + v g = (f + N (v f)) + (g + N (v g)) :=
            congrArg₂ (· + ·) (fixedPoint_equation F μ H S hS hcontr M hsem I f)
              (fixedPoint_equation F μ H S hS hcontr M hsem I g)
          _ = f + g + N (v f + v g) := by rw [convolution_add F μ H S hS hcontr M hsem I]; abel
      map_smul' := fun c f => by
        symm
        apply fixedPoint_unique F μ H S hS hcontr M hsem I
        calc
          c • v f = c • (f + N (v f)) := congrArg (c • ·) (fixedPoint_equation F μ H S hS hcontr M hsem I f)
          _ = c • f + N (c • v f) := by rw [smul_add, convolution_smul F μ H S hS hcontr M hsem I] }
  exact lin.mkContinuous (HeatVolterraUniformEnergy.stabilityConstant H M) fun f =>
    HeatVolterraUniformEnergy.fixed_point_bound F μ H S hS hcontr M hsem I f (v f)
      (fixedPoint_equation F μ H S hS hcontr M hsem I f)

include hS hcontr in
theorem solve_equation (f : Proc) :
    solve F μ H S hS hcontr M hsem I f = f + N (solve F μ H S hS hcontr M hsem I f) :=
  fixedPoint_equation F μ H S hS hcontr M hsem I f

include hS hcontr in
theorem eq_solve (f u : Proc) (hu : u = f + N u) : u = solve F μ H S hS hcontr M hsem I f :=
  fixedPoint_unique F μ H S hS hcontr M hsem I f u hu

end HeatVolterraSolutionLinear

#print axioms HeatVolterraSolutionLinear.orbit
#print axioms HeatVolterraSolutionLinear.sliceOperator
#print axioms HeatVolterraSolutionLinear.solve_equation
#print axioms HeatVolterraSolutionLinear.eq_solve
