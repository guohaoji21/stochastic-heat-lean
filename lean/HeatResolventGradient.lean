import HeatRegularizedWeakEquation
import SHE.ProcessEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace HeatResolventGradient
open MeasureTheory EllipticPdes HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolventForm
open HeatDirichletResolvent HeatRegularizedWeakEquation
open scoped ENNReal

def lift (a : ℝ) (ha : 1≤a) : Base →L[ℝ] H01 := a • HeatDirichletResolventForm.lift a ha

def gradient (a : ℝ) (ha : 1≤a) : Base →L[ℝ] Base :=
  H1Graph.gradL.comp ((H1Graph.H01 (volume : Measure ℝ) domain).subtypeL.comp (lift a ha))

theorem embed_lift {a : ℝ} (ha : 1≤a) (x : Base) : embed (lift a ha x)=smoothing a ha x := by
  change embed (a • HeatDirichletResolventForm.lift a ha x)=a • embed (HeatDirichletResolventForm.lift a ha x)
  exact embed.map_smul a _

theorem norm_decomposition {a : ℝ} (ha : 1≤a) (x : Base) :
    ‖lift a ha x‖^2=‖smoothing a ha x‖^2+‖gradient a ha x‖^2 := by
  have he := H1Graph.norm_sq_eq (lift a ha x : H1Graph volume domain)
  change ‖lift a ha x‖^2=‖embed (lift a ha x)‖^2+‖gradient a ha x‖^2 at he
  rw [embed_lift] at he
  exact he

theorem drift_energy {a : ℝ} (ha : 1≤a) (x : Base) :
    inner ℝ (derivative a ha x) (smoothing a ha x)=-‖gradient a ha x‖^2 := by
  obtain ⟨U,hU,hform⟩ := smoothing_graph ha x
  have hUeq : U=lift a ha x := h01_function_injective (hU.trans (embed_lift ha x).symm)
  subst U
  have he := hform (lift a ha x)
  change inner ℝ (gradient a ha x) (gradient a ha x)=-inner ℝ (derivative a ha x) (embed (lift a ha x)) at he
  rw [real_inner_self_eq_norm_sq,embed_lift] at he
  linarith

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

theorem lp_norm_decomposition {a : ℝ} (ha : 1≤a) (u : Lp Base 2 ν) :
    ‖((lift a ha).compLpL 2 ν) u‖^2=
      ‖((smoothing a ha).compLpL 2 ν) u‖^2+‖((gradient a ha).compLpL 2 ν) u‖^2 := by
  rw [SHE.PredictableL2.realLp_norm_sq,SHE.PredictableL2.realLp_norm_sq,SHE.PredictableL2.realLp_norm_sq]
  rw [←integral_add (Lp.memLp (((smoothing a ha).compLpL 2 ν) u)).norm.integrable_sq
    (Lp.memLp (((gradient a ha).compLpL 2 ν) u)).norm.integrable_sq]
  apply integral_congr_ae
  filter_upwards [(lift a ha).coeFn_compLpL u,(smoothing a ha).coeFn_compLpL u,
    (gradient a ha).coeFn_compLpL u] with x hl hs hg
  rw [hl]
  change ‖lift a ha (u x)‖^2=‖((smoothing a ha).compLpL 2 ν) u x‖^2+‖((gradient a ha).compLpL 2 ν) u x‖^2
  rw [hs,hg]
  exact norm_decomposition ha _

theorem lp_drift_energy {a : ℝ} (ha : 1≤a) (u : Lp Base 2 ν) :
    inner ℝ (((derivative a ha).compLpL 2 ν) u) (((smoothing a ha).compLpL 2 ν) u)=
      -‖((gradient a ha).compLpL 2 ν) u‖^2 := by
  rw [L2.inner_def,SHE.PredictableL2.realLp_norm_sq,←integral_neg]
  apply integral_congr_ae
  filter_upwards [(derivative a ha).coeFn_compLpL u,(smoothing a ha).coeFn_compLpL u,
    (gradient a ha).coeFn_compLpL u] with x hd hs hg
  rw [hd,hs,hg]
  exact drift_energy ha _

end HeatResolventGradient
#check @HeatResolventGradient.embed_lift
#print axioms HeatResolventGradient.embed_lift
#check @HeatResolventGradient.norm_decomposition
#print axioms HeatResolventGradient.norm_decomposition
#check @HeatResolventGradient.drift_energy
#print axioms HeatResolventGradient.drift_energy
#check @HeatResolventGradient.lp_norm_decomposition
#print axioms HeatResolventGradient.lp_norm_decomposition
#check @HeatResolventGradient.lp_drift_energy
#print HeatResolventGradient.lp_drift_energy
#print axioms HeatResolventGradient.lp_drift_energy
