import HeatPolynomialBarrier
import HeatSubeigenEuler
import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatBarrierGraph
open MeasureTheory Set Filter EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatPolynomialBarrier

theorem compact_support {a b : ℝ} (hab : a≤b) : HasCompactSupport (bump a b) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (support_subset a b hab)

theorem gradient_compact {a b : ℝ} (hab : a≤b) : HasCompactSupport (HeatPolynomialBarrier.gradient a b) := by
  have he : deriv (bump a b)=HeatPolynomialBarrier.gradient a b := funext (bump_deriv a b · |>.deriv)
  rw [←he]
  exact (compact_support hab).deriv

theorem laplacian_compact {a b : ℝ} (hab : a≤b) : HasCompactSupport (laplacian a b) := by
  have he : deriv (HeatPolynomialBarrier.gradient a b)=laplacian a b := funext (gradient_deriv a b · |>.deriv)
  rw [←he]
  exact (gradient_compact hab).deriv

theorem bump_weak (a b : ℝ) :
    HasWeakFDerivOn ⊤ (bump a b) (fun x => innerSL ℝ (HeatPolynomialBarrier.gradient a b x)) volume := by
  have h := hasWeakFDerivOn_fderiv (Ω := (⊤ : TopologicalSpace.Opens ℝ)) (μ := volume) ((bump_contDiff a b).of_le (by norm_num : (1:WithTop ℕ∞)≤2)).contDiffOn
  apply h.congr_ae Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall fun x => by
    rw [(bump_deriv a b x).hasFDerivAt.fderiv]
    ext v
    simp [Real.inner_apply,mul_comm]

theorem gradient_weak (a b : ℝ) :
    HasWeakFDerivOn ⊤ (HeatPolynomialBarrier.gradient a b) (fun x => innerSL ℝ (laplacian a b x)) volume := by
  have h := hasWeakFDerivOn_fderiv (Ω := (⊤ : TopologicalSpace.Opens ℝ)) (μ := volume) (gradient_contDiff a b).contDiffOn
  apply h.congr_ae Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall fun x => by
    rw [(gradient_deriv a b x).hasFDerivAt.fderiv]
    ext v
    simp [Real.inner_apply,mul_comm]

variable (a b : ℝ) (hab : a≤b)
include hab in
theorem fMem : MemLp (bump a b) 2 baseMeasure :=
  ((bump_contDiff a b).continuous.memLp_of_hasCompactSupport (compact_support hab)).mono_measure Measure.restrict_le_self

include hab in
theorem dMem : MemLp (HeatPolynomialBarrier.gradient a b) 2 baseMeasure :=
  ((gradient_contDiff a b).continuous.memLp_of_hasCompactSupport (gradient_compact hab)).mono_measure Measure.restrict_le_self

include hab in
theorem gMem : MemLp (laplacian a b) 2 baseMeasure := by
  have hc : Continuous (laplacian a b) := by unfold laplacian ddp dp q dq;fun_prop
  exact (hc.memLp_of_hasCompactSupport (laplacian_compact hab)).mono_measure Measure.restrict_le_self

def f : Base := (fMem a b hab).toLp (bump a b)
def d : Base := (dMem a b hab).toLp (HeatPolynomialBarrier.gradient a b)
def g : Base := (gMem a b hab).toLp (laplacian a b)

theorem weak_graph (ha : 0<a) (hb : b<10) : weakLaplacian (f a b hab) (g a b hab) := by
  have hfm := (bump_contDiff a b).continuous.memLp_of_hasCompactSupport (compact_support hab) (μ := volume) (p := 2)
  have hdm := (gradient_contDiff a b).continuous.memLp_of_hasCompactSupport (gradient_compact hab) (μ := volume) (p := 2)
  have hmem : H1Graph.mk (f a b hab) (d a b hab) ∈ H1Graph.H01 volume domain :=
    H1Graph.mem_H01_of_hasCompactSupport isOpen_Ioo (bump_weak a b) hfm hdm (compact_support hab)
      (fun x hx => ⟨lt_of_lt_of_le ha ((support_subset a b hab hx).1),
        lt_of_le_of_lt ((support_subset a b hab hx).2) hb⟩)
  let U : H01 := ⟨H1Graph.mk (f a b hab) (d a b hab),hmem⟩
  apply HeatWeakSecondDerivative.weakLaplacian_of_second_weak_derivative _ _ U rfl
  have hw := (gradient_weak a b).mono (by simp : (⟨domain,isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ)≤⊤)
  apply hw.congr_ae ((dMem a b hab).coeFn_toLp).symm
  filter_upwards [(gMem a b hab).coeFn_toLp] with x hx
  change (innerSL ℝ) (laplacian a b x)=(innerSL ℝ) (((gMem a b hab).toLp (laplacian a b)) x)
  rw [hx]

theorem nonnegative : ∀ᵐ x ∂baseMeasure,0 ≤ f a b hab x := by
  filter_upwards [(fMem a b hab).coeFn_toLp] with x hx
  change 0 ≤ ((fMem a b hab).toLp (bump a b)) x
  rw [hx]
  exact HeatPolynomialBarrier.nonnegative a b x

theorem subeigen (hlt : a<b) : ∀ᵐ x ∂baseMeasure,0 ≤ (g a b hab+(196/(b-a)^2) • f a b hab) x := by
  filter_upwards [(fMem a b hab).coeFn_toLp,(gMem a b hab).coeFn_toLp,
    Lp.coeFn_smul (196/(b-a)^2) (f a b hab),Lp.coeFn_add (g a b hab) ((196/(b-a)^2) • f a b hab)] with x hf hg hs hadd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  change 0 ≤ ((gMem a b hab).toLp (laplacian a b)) x+196/(b-a)^2*((fMem a b hab).toLp (bump a b)) x
  rw [hf,hg]
  exact HeatPolynomialBarrier.subeigen hlt x

theorem heat_lower (ha : 0<a) (hb : b<10) (hlt : a<b) (T : ℝ) (hT : 0≤T) :
    ∀ᵐ x ∂baseMeasure,0 ≤ (paperHeat T (f a b hab)-Real.exp (-T*(196/(b-a)^2)) • f a b hab) x :=
  HeatSubeigenEuler.heat_barrier T hT _ (by positivity) _ _ (weak_graph a b hab ha hb) (subeigen a b hab hlt)

end HeatBarrierGraph
#check @HeatBarrierGraph.weak_graph
#print axioms HeatBarrierGraph.weak_graph
#check @HeatBarrierGraph.heat_lower
#print HeatBarrierGraph.heat_lower
#print axioms HeatBarrierGraph.heat_lower
