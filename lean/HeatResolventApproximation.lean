import HeatDirichletResolvent
import HeatContractionDenseLimit
import Mathlib.Analysis.InnerProductSpace.Symmetric

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatResolventApproximation
open MeasureTheory Filter HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolvent
open scoped Topology

theorem kernel_zero {a : ℝ} (ha : 1≤a) (f : Base) (hf : resolvent a ha f=0) : f=0 := by
  have hg := weak_graph ha f
  rw [hf,smul_zero,zero_sub] at hg
  exact neg_eq_zero.mp (weakLaplacian_unique 0 (-f) 0 hg HeatWeakDirichletAlgebra.zero)

theorem injective {a : ℝ} (ha : 1≤a) : Function.Injective (resolvent a ha) := by
  intro f g he
  apply sub_eq_zero.mp
  apply kernel_zero ha
  rw [map_sub,he,sub_self]

theorem dense_range {a : ℝ} (ha : 1≤a) : DenseRange (resolvent a ha) := by
  let R := resolvent a ha
  have hk : R.toLinearMap.ker=⊥ := LinearMap.ker_eq_bot.mpr (injective ha)
  have hs : R.toLinearMap.IsSymmetric := symmetric ha
  have ho := LinearMap.IsSymmetric.orthogonal_range hs
  have hc := R.toLinearMap.range.orthogonal_orthogonal_eq_closure
  rw [ho,hk,Submodule.bot_orthogonal_eq_top] at hc
  change Dense (R.toLinearMap.range : Set Base)
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hc.symm

theorem inverts {a : ℝ} (ha : 1≤a) (f g : Base) (hfg : weakLaplacian f g) :
    resolvent a ha (a • f-g)=f := by
  let r := resolvent a ha (a • f-g)
  have hr : weakLaplacian r (a • r-(a • f-g)) := weak_graph ha _
  have hneg : weakLaplacian (-f) (-g) := by
    simpa only [neg_one_smul] using HeatWeakDirichletAlgebra.smul (-1) f g hfg
  have hw : weakLaplacian (r-f) ((a • r-(a • f-g))-g) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using
      HeatWeakDirichletAlgebra.add r (a • r-(a • f-g)) (-f) (-g) hr
        hneg
  have hd := weakLaplacian_dissipative _ _ hw
  have he : (a • r-(a • f-g))-g=a • (r-f) := by rw [smul_sub];abel
  rw [he,real_inner_smul_left,real_inner_self_eq_norm_sq] at hd
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hz : ‖r-f‖=0 := by nlinarith [sq_nonneg ‖r-f‖,norm_nonneg (r-f)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem smoothing_difference {a : ℝ} (ha : 1≤a) (f g : Base) (hfg : weakLaplacian f g) :
    smoothing a ha f-f=resolvent a ha g := by
  have he := inverts ha f g hfg
  rw [map_sub,map_smul] at he
  change a • resolvent a ha f-resolvent a ha g=f at he
  change a • resolvent a ha f-f=resolvent a ha g
  rw [sub_eq_iff_eq_add.mp he]
  abel

def approx (n : ℕ) : Base →L[ℝ] Base := smoothing ((n:ℝ)+1) (by have hn := Nat.cast_nonneg (α := ℝ) n;linarith)

theorem tendsto_on_domain (f g : Base) (hfg : weakLaplacian f g) :
    Tendsto (fun n => approx n f) atTop (𝓝 f) := by
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => ‖g‖/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul ‖g‖
  have hz : Tendsto (fun n => ‖approx n f-f‖) atTop (𝓝 (0:ℝ)) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => by
      rw [approx,smoothing_difference (by have hn := Nat.cast_nonneg (α := ℝ) n;linarith : 1≤(n:ℝ)+1) f g hfg]
      exact norm_bound _ g) hb
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hz

theorem tendsto_identity (f : Base) : Tendsto (fun n => approx n f) atTop (𝓝 f) := by
  apply HeatContractionDenseLimit.tendsto_of_dense approx
    (fun n x => smoothing_contraction (by have hn := Nat.cast_nonneg (α := ℝ) n;linarith) x) (resolvent 1 le_rfl) (dense_range le_rfl)
  intro g
  exact tendsto_on_domain _ _ (weak_graph le_rfl g)

end HeatResolventApproximation
#check @HeatResolventApproximation.kernel_zero
#print axioms HeatResolventApproximation.kernel_zero
#check @HeatResolventApproximation.injective
#print axioms HeatResolventApproximation.injective
#check @HeatResolventApproximation.dense_range
#print axioms HeatResolventApproximation.dense_range
#check @HeatResolventApproximation.inverts
#print axioms HeatResolventApproximation.inverts
#check @HeatResolventApproximation.smoothing_difference
#print axioms HeatResolventApproximation.smoothing_difference
#check @HeatResolventApproximation.tendsto_on_domain
#print axioms HeatResolventApproximation.tendsto_on_domain
#check @HeatResolventApproximation.tendsto_identity
#print HeatResolventApproximation.tendsto_identity
#print axioms HeatResolventApproximation.tendsto_identity
