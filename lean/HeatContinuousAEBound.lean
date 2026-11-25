import SHEStochastic.ContinuousEqualityBeforeExit

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatContinuousAEBound
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem bound {A : Type*} [TopologicalSpace A] [SeparableSpace A]
    (X : A → Ω → ℝ) (B : Ω → ℝ) (hc : ∀ᵐ ω ∂μ, Continuous (X · ω))
    (hb : ∀ t, ∀ᵐ ω ∂μ, X t ω≤B ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω≤B ω := by
  let D (t : A) (ω : Ω) := max (X t ω-B ω) 0
  have hdc : ∀ᵐ ω ∂μ, Continuous (D · ω) := by
    filter_upwards [hc] with ω hω
    exact (hω.sub continuous_const).max continuous_const
  have hd (t : A) : ∀ᵐ ω ∂μ, edist (D t ω) (0:ℝ)=0 := by
    filter_upwards [hb t] with ω ht
    simp only [D,max_eq_right (sub_nonpos.mpr ht),edist_self]
  have he := indistinguishable_of_edist_modification hdc
    (Eventually.of_forall (fun _ : Ω => (continuous_const : Continuous (fun _ : A => (0:ℝ))))) hd
  filter_upwards [he] with ω hω t
  have hz : max (X t ω-B ω) 0=0 := edist_eq_zero.mp (hω t)
  have hh := le_max_left (X t ω-B ω) 0
  rw [hz] at hh
  linarith

end HeatContinuousAEBound
#check @HeatContinuousAEBound.bound
#print HeatContinuousAEBound.bound
#print axioms HeatContinuousAEBound.bound
