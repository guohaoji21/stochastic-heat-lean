import HeatWeakSecondDerivative
import EllipticPdes.Sobolev.GraphLattice
import Mathlib.Analysis.InnerProductSpace.NormPow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatPolynomialBarrier
open MeasureTheory Set Filter EllipticPdes HeatIntervalNormalization HeatWeakDirichlet
open scoped Topology

def p (x : ℝ) : ℝ := (x^4+x*|x|^3)/2
def dp (x : ℝ) : ℝ := 2*(x^3+|x|^3)
def ddp (x : ℝ) : ℝ := 6*(x^2+x*|x|)

theorem abs_cube_deriv (x : ℝ) : HasDerivAt (fun y : ℝ => |y|^3) (3*|x| * x) x := by
  have h := hasDerivAt_abs_rpow x (by norm_num : (1:ℝ)<3)
  norm_num only [show (3:ℝ)-2=1 by norm_num,Real.rpow_one] at h
  simpa only [Real.rpow_ofNat] using h

theorem p_deriv (x : ℝ) : HasDerivAt p (dp x) x := by
  have h := (((hasDerivAt_id x).pow 4).add ((hasDerivAt_id x).mul (abs_cube_deriv x))).div_const 2
  convert h using 1
  · rfl
  · dsimp [dp]
    have ha : |x|^3=|x| * x^2 := by rw [pow_succ,sq_abs];ring
    norm_num only at *
    rw [ha]
    ring

theorem dp_deriv (x : ℝ) : HasDerivAt dp (ddp x) x := by
  have h := (((hasDerivAt_id x).pow 3).add (abs_cube_deriv x)).const_mul 2
  convert h using 1
  · rfl
  · dsimp only [ddp]
    norm_num only [id_eq]
    ring

theorem dp_contDiff : ContDiff ℝ 1 dp := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (dp_deriv x).differentiableAt,?_⟩
  have he : deriv dp=ddp := funext fun x => (dp_deriv x).deriv
  rw [he]
  unfold ddp
  fun_prop

theorem p_contDiff : ContDiff ℝ 2 p := by
  rw [show (2:WithTop ℕ∞)=1+1 by norm_num,contDiff_succ_iff_deriv]
  refine ⟨fun x => (p_deriv x).differentiableAt,by simp,?_⟩
  convert dp_contDiff using 1
  exact funext fun x => (p_deriv x).deriv

theorem formulas_nonnegative {x : ℝ} (hx : 0 ≤ x) :
    p x=x^4 ∧ dp x=4*x^3 ∧ ddp x=12*x^2 := by
  simp only [p,dp,ddp,abs_of_nonneg hx]
  constructor
  · ring
  · constructor <;> ring

theorem formulas_nonpositive {x : ℝ} (hx : x ≤ 0) : p x=0 ∧ dp x=0 ∧ ddp x=0 := by
  simp only [p,dp,ddp,abs_of_nonpos hx]
  constructor
  · ring
  · constructor <;> ring

def q (a b x : ℝ) : ℝ := (x-a)*(b-x)
def dq (a b x : ℝ) : ℝ := a+b-2*x
def bump (a b : ℝ) (x : ℝ) : ℝ := p (q a b x)
def gradient (a b : ℝ) (x : ℝ) : ℝ := dp (q a b x)*dq a b x
def laplacian (a b : ℝ) (x : ℝ) : ℝ := ddp (q a b x)*(dq a b x)^2-2*dp (q a b x)

theorem q_deriv (a b x : ℝ) : HasDerivAt (q a b) (dq a b x) x := by
  convert ((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_const x b).sub (hasDerivAt_id x)) using 1
  · rfl
  · dsimp [dq];ring

theorem bump_deriv (a b x : ℝ) : HasDerivAt (bump a b) (gradient a b x) x :=
  (p_deriv (q a b x)).comp x (q_deriv a b x)

theorem gradient_deriv (a b x : ℝ) : HasDerivAt (gradient a b) (laplacian a b x) x := by
  have hd : HasDerivAt (dq a b) (-2) x := by
    convert (hasDerivAt_const x (a+b)).sub ((hasDerivAt_id x).const_mul 2) using 1
    · funext y;rfl
    · norm_num
  convert ((dp_deriv (q a b x)).comp x (q_deriv a b x)).mul hd using 1
  · rfl
  · dsimp [laplacian];ring

theorem bump_contDiff (a b : ℝ) : ContDiff ℝ 2 (bump a b) :=
  p_contDiff.comp (by unfold q;fun_prop)

theorem gradient_contDiff (a b : ℝ) : ContDiff ℝ 1 (gradient a b) := by
  unfold gradient
  exact (dp_contDiff.comp (by unfold q;fun_prop)).mul (by unfold dq;fun_prop)

theorem support_subset (a b : ℝ) (hab : a ≤ b) : tsupport (bump a b) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  have hq : q a b x ≤ 0 := by
    simp only [mem_Icc,not_and_or,not_le] at hn
    rcases hn with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  exact hx ((formulas_nonpositive hq).1)

theorem gradient_zero_outside (a b x : ℝ) (hab : a ≤ b) (hx : x ∉ Icc a b) : gradient a b x=0 := by
  have hb := support_subset a b hab
  have he : (bump a b) =ᶠ[𝓝 x] 0 :=
    Filter.mem_of_superset (isClosed_Icc.isOpen_compl.mem_nhds hx) (fun y hy => by
      have hn : y ∉ tsupport (bump a b) := fun h => hy (hb h)
      exact image_eq_zero_of_notMem_tsupport hn)
  rw [←(bump_deriv a b x).deriv]
  simpa only [deriv_zero,Pi.zero_apply] using he.deriv_eq

theorem nonnegative (a b x : ℝ) : 0 ≤ bump a b x := by
  rcases le_total 0 (q a b x) with h | h
  · rw [bump,(formulas_nonnegative h).1];positivity
  · rw [bump,(formulas_nonpositive h).1]

theorem subeigen {a b : ℝ} (hab : a<b) (x : ℝ) :
    0 ≤ laplacian a b x+(196/(b-a)^2)*bump a b x := by
  rcases le_total 0 (q a b x) with hq | hq
  · obtain ⟨h1,h2,h3⟩ := formulas_nonnegative hq
    have hL : (b-a)^2>0 := sq_pos_of_pos (by linarith)
    have he : (dq a b x)^2=(b-a)^2-4*q a b x := by unfold dq q;ring
    dsimp only [laplacian,bump]
    rw [h1,h2,h3,he]
    have hz := sq_nonneg (14*q a b x-2*(b-a)^2)
    apply (mul_nonneg_iff_of_pos_right hL).mp
    field_simp
    nlinarith [mul_nonneg (sq_nonneg (q a b x)) (sq_nonneg (b-a)),
      mul_nonneg (sq_nonneg (q a b x)) hz]
  · obtain ⟨h1,h2,h3⟩ := formulas_nonpositive hq
    simp [laplacian,bump,h1,h2,h3]

end HeatPolynomialBarrier
#check @HeatPolynomialBarrier.p_deriv
#print axioms HeatPolynomialBarrier.p_deriv
#check @HeatPolynomialBarrier.p_contDiff
#print axioms HeatPolynomialBarrier.p_contDiff
#check @HeatPolynomialBarrier.subeigen
#print HeatPolynomialBarrier.subeigen
#print axioms HeatPolynomialBarrier.subeigen
