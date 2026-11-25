import HeatWeakDirichlet
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section
namespace HeatGeneratorDissipative
open HeatIntervalNormalization
open scoped RealInnerProductSpace

def generator (f g : Base) : Prop :=
  HasDerivWithinAt (fun t : ℝ => paperHeat t f) g (Set.Ici 0) 0

theorem norm_sq_antitone (f : Base) :
    AntitoneOn (fun t : ℝ => ‖paperHeat t f‖^2) (Set.Ici 0) := by
  intro s hs t ht hst
  have hst' : 0 ≤ t-s := sub_nonneg.mpr hst
  have h := paperHeat_contraction (t-s) (paperHeat s f)
  have he : paperHeat t f = paperHeat (t-s) (paperHeat s f) := by
    have hsem := paperHeat_semigroup hst' hs
    have heq : t-s+s=t := by ring
    rw [heq] at hsem
    exact congrFun (congrArg DFunLike.coe hsem) f
  change ‖paperHeat t f‖^2 ≤ ‖paperHeat s f‖^2
  rw [he]
  nlinarith [norm_nonneg (paperHeat (t-s) (paperHeat s f)), norm_nonneg (paperHeat s f)]

theorem generator_dissipative (f g : Base) (h : generator f g) : inner ℝ g f ≤ 0 := by
  have hd := HasDerivWithinAt.inner ℝ h h
  have hz : paperHeat 0 f = f := by rw [paperHeat_zero]; rfl
  rw [hz] at hd
  have ha := (norm_sq_antitone f).derivWithin_nonpos (x := (0 : ℝ))
  have hdNorm : HasDerivWithinAt (fun t : ℝ => ‖paperHeat t f‖^2)
      (inner ℝ f g + inner ℝ g f) (Set.Ici 0) 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hd
  have hd' := hdNorm.derivWithin (uniqueDiffOn_Ici 0 0 (Set.mem_Ici.mpr le_rfl))
  rw [hd'] at ha
  have hc := real_inner_comm f g
  linarith

theorem generator_pair_dissipative (f g u v : Base)
    (hfg : generator f g) (huv : generator u v) : inner ℝ (g-v) (f-u) ≤ 0 := by
  apply generator_dissipative
  unfold generator at *
  have hs := hfg.sub huv
  have he : ((fun t : ℝ => paperHeat t f) - (fun t => paperHeat t u)) =
      (fun t => paperHeat t (f-u)) := by
    funext t
    simp only [Pi.sub_apply, map_sub]
  rw [he] at hs
  exact hs

theorem generator_eq_weak_of_inclusion
    (hinclude : ∀ f g : Base, HeatWeakDirichlet.weakLaplacian f g → generator f g)
    (f g : Base) : generator f g ↔ HeatWeakDirichlet.weakLaplacian f g := by
  constructor
  · exact HeatWeakDirichlet.weakLaplacian_no_dissipative_extension generator hinclude
      generator_pair_dissipative f g
  · exact hinclude f g

end HeatGeneratorDissipative
#check @HeatGeneratorDissipative.generator_dissipative
#print axioms HeatGeneratorDissipative.generator_dissipative
#check @HeatGeneratorDissipative.generator_pair_dissipative
#print axioms HeatGeneratorDissipative.generator_pair_dissipative

#check @HeatGeneratorDissipative.norm_sq_antitone
#print axioms HeatGeneratorDissipative.norm_sq_antitone
#check @HeatGeneratorDissipative.generator_eq_weak_of_inclusion
#print axioms HeatGeneratorDissipative.generator_eq_weak_of_inclusion
