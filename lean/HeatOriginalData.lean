import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace HeatOriginalData
open Set Metric

theorem exists_cutoff_and_initial : ∃ b g : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ tsupport b⊆Ioo (6:ℝ) 7 ∧
    (∀ x,0 ≤ b x) ∧ (∀ x,b x ≤ 1) ∧ (∀ x∈Ioo (25/4:ℝ) (27/4),b x=1) ∧
    ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g⊆Ioo (25/4:ℝ) (27/4) ∧
    (∀ x,0 ≤ g x) ∧ g≠0 := by
  let B : ContDiffBump (13/2:ℝ) := ⟨3/10,2/5,by norm_num,by norm_num⟩
  let G : ContDiffBump (13/2:ℝ) := ⟨1/10,1/5,by norm_num,by norm_num⟩
  have hBsupport : tsupport B⊆Ioo (6:ℝ) 7 := by
    intro x hx
    rw [B.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,abs_le] at hx
    dsimp only [B] at hx
    constructor <;> linarith [hx.1,hx.2]
  have hBone : ∀ x∈Ioo (25/4:ℝ) (27/4),B x=1 := by
    intro x hx
    apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall,Real.dist_eq,abs_le]
    dsimp only [B]
    constructor <;> linarith [hx.1,hx.2]
  have hGsupport : tsupport G⊆Ioo (25/4:ℝ) (27/4) := by
    intro x hx
    rw [G.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,abs_le] at hx
    dsimp only [G] at hx
    constructor <;> linarith [hx.1,hx.2]
  have hGcenter : G (13/2)=1 := G.one_of_mem_closedBall (by simp [G,Metric.mem_closedBall])
  have hGne : (G : ℝ → ℝ)≠0 := by
    intro he
    have hz := congrFun he (13/2)
    rw [hGcenter] at hz
    norm_num at hz
  exact ⟨B,G,B.contDiff,B.hasCompactSupport,hBsupport,B.nonneg',fun _ => B.le_one,hBone,
    G.contDiff,G.hasCompactSupport,hGsupport,G.nonneg',hGne⟩

end HeatOriginalData
#check @HeatOriginalData.exists_cutoff_and_initial
#print axioms HeatOriginalData.exists_cutoff_and_initial
