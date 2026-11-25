import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false
noncomputable section
namespace HeatContractionDenseLimit
open Filter
open scoped Topology
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendsto_of_dense (A : ℕ → E →L[ℝ] E) (hA : ∀ n x, ‖A n x‖≤‖x‖)
    (R : P → E) (hR : DenseRange R)
    (hlim : ∀ p, Tendsto (fun n => A n (R p)) atTop (𝓝 (R p))) (x : E) :
    Tendsto (fun n => A n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v,⟨p,rfl⟩,hp⟩ := Metric.mem_closure_iff.mp (hR x) (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hlim p) (ε/2) (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hdist : dist (A n x) (A n (R p))≤dist x (R p) := by
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact hA n _
  have hp' : dist (R p) x<ε/4 := by rw [dist_comm];exact hp
  have ht := dist_triangle (A n x) (A n (R p)) x
  have hs := dist_triangle (A n (R p)) (R p) x
  have hl := hN n hn
  linarith

end HeatContractionDenseLimit
#check @HeatContractionDenseLimit.tendsto_of_dense
#print HeatContractionDenseLimit.tendsto_of_dense
#print axioms HeatContractionDenseLimit.tendsto_of_dense
