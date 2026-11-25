import HeatBarrierNonzero
import HeatWeakDirichletAlgebra
import HeatScalarMultiplier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace HeatBarrierChoice
open MeasureTheory Set Filter HeatIntervalNormalization HeatPolynomialBarrier HeatWeakDirichlet

/-- A positive continuous initial state has a closed interior interval on which it has a positive lower bound. -/
theorem interval_inside {u : ℝ → ℝ} (hu : Continuous u) (hpos : ∀ x,0≤u x) (hne : u≠0)
    (hsupp : tsupport u⊆Ioo (25/4:ℝ) (27/4)) :
    ∃ a b δ : ℝ, (25/4:ℝ)<a ∧ a<b ∧ b<(27/4:ℝ) ∧ 0<δ ∧ ∀ x∈Icc a b,δ≤u x := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hne
  have hx' : u x≠0 := hx
  have hux : 0<u x := lt_of_le_of_ne (hpos x) (Ne.symm hx')
  have hin : x∈Ioo (25/4:ℝ) (27/4) := hsupp (subset_tsupport u hx')
  let V := Ioo (25/4:ℝ) (27/4) ∩ u ⁻¹' Ioi (u x/2)
  have hV : IsOpen V := isOpen_Ioo.inter (isOpen_Ioi.preimage hu)
  have hxV : x∈V := ⟨hin,by change u x/2<u x;linarith⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  let a := x-ε/2
  let b := x+ε/2
  have hmem : ∀ y∈Icc a b,y∈V := by
    intro y hy
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [a,b] at hy
    constructor <;> linarith [hy.1,hy.2]
  have hab : a<b := by dsimp [a,b];linarith
  have ha := (hmem a ⟨le_rfl,hab.le⟩).1
  have hb := (hmem b ⟨hab.le,le_rfl⟩).1
  exact ⟨a,b,u x/2,ha.1,hab,hb.2,by positivity,fun y hy => ((hmem y hy).2).le⟩

theorem scaled_bound {a b δ : ℝ} (hab : a≤b) (hδ : 0<δ) (u : ℝ → ℝ)
    (hu : ∀ x,0≤u x) (hmin : ∀ x∈Icc a b,δ≤u x) :
    ∀ x,(δ/((b-a)^8+1))*bump a b x≤u x := by
  intro x
  have hden : 0<(b-a)^8+1 := by positivity
  have hc : 0≤δ/((b-a)^8+1) := div_nonneg hδ.le hden.le
  by_cases hx : x∈Icc a b
  · have hprod := mul_le_mul_of_nonneg_left (HeatBarrierNonzero.bump_bound hab x) hc
    have hcoeff : δ/((b-a)^8+1)*(b-a)^8≤δ := by
      calc
        _ ≤ δ/((b-a)^8+1)*((b-a)^8+1) := mul_le_mul_of_nonneg_left (by linarith) hc
        _ = δ := div_mul_cancel₀ _ hden.ne'
    exact hprod.trans (hcoeff.trans (hmin x hx))
  · have hz : bump a b x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (support_subset a b hab h))
    rw [hz,mul_zero]
    exact hu x

end HeatBarrierChoice
#check @HeatBarrierChoice.interval_inside
#print axioms HeatBarrierChoice.interval_inside
#check @HeatBarrierChoice.scaled_bound
#print HeatBarrierChoice.scaled_bound
#print axioms HeatBarrierChoice.scaled_bound
