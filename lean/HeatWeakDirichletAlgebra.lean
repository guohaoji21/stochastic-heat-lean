import HeatWeakDirichlet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatWeakDirichletAlgebra
open MeasureTheory EllipticPdes HeatIntervalNormalization HeatWeakDirichlet

theorem zero : weakLaplacian 0 0 := by
  refine ⟨0,by simp,?_⟩
  intro V
  simp only [Submodule.coe_zero,map_zero,inner_zero_left,neg_zero]

theorem add (f g u v : Base) (hfg : weakLaplacian f g) (huv : weakLaplacian u v) :
    weakLaplacian (f+u) (g+v) := by
  obtain ⟨U,hU,hformU⟩ := hfg
  obtain ⟨V,hV,hformV⟩ := huv
  refine ⟨U+V,?_,?_⟩
  · rw [map_add,hU,hV]
  · intro W
    simp only [Submodule.coe_add,map_add,inner_add_left]
    rw [hformU W,hformV W]
    ring

theorem smul (c : ℝ) (f g : Base) (hfg : weakLaplacian f g) :
    weakLaplacian (c • f) (c • g) := by
  obtain ⟨U,hU,hform⟩ := hfg
  refine ⟨c • U,?_,?_⟩
  · rw [map_smul,hU]
  · intro V
    simp only [Submodule.coe_smul,map_smul,real_inner_smul_left]
    rw [hform V]
    ring

end HeatWeakDirichletAlgebra
#check @HeatWeakDirichletAlgebra.zero
#print axioms HeatWeakDirichletAlgebra.zero
#check @HeatWeakDirichletAlgebra.add
#print axioms HeatWeakDirichletAlgebra.add
#check @HeatWeakDirichletAlgebra.smul
#print HeatWeakDirichletAlgebra.smul
#print axioms HeatWeakDirichletAlgebra.smul
