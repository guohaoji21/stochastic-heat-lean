import HeatFourierFrameConvergence
import Mathlib.Analysis.Convex.Integral

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace HeatPositiveCone
open MeasureTheory Filter HeatIntervalNormalization
open scoped Topology

def cone : Set Base := {f | ∀ᵐ x ∂baseMeasure,0≤f x}

theorem closed : IsClosed cone := by
  apply isSeqClosed_iff_isClosed.mp
  intro u f hu ht
  exact HeatFourierFrameConvergence.nonnegative_limit u f ht hu

theorem convex : Convex ℝ cone := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf,hg,Lp.coeFn_add (a • f) (b • g),Lp.coeFn_smul a f,Lp.coeFn_smul b g] with x hfx hgx hadd hfa hgb
  rw [hadd]
  change 0≤(a • f) x+(b • g) x
  rw [hfa,hgb]
  exact add_nonneg (mul_nonneg ha hfx) (mul_nonneg hb hgx)

theorem integral_nonnegative {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → Base) (hf : Integrable f ν) (hp : ∀ᵐ v ∂ν,∀ᵐ x ∂baseMeasure,0≤f v x) :
    ∀ᵐ x ∂baseMeasure,0≤(∫ v,f v ∂ν) x :=
  Convex.integral_mem convex closed hp hf

theorem monotone (A : Base →L[ℝ] Base)
    (hA : ∀ f : Base,(∀ᵐ x ∂baseMeasure,0≤f x) → ∀ᵐ x ∂baseMeasure,0≤A f x)
    (f g : Base) (hfg : ∀ᵐ x ∂baseMeasure,f x≤g x) :
    ∀ᵐ x ∂baseMeasure,A f x≤A g x := by
  have hsub : ∀ᵐ x ∂baseMeasure,0≤(g-f) x := by
    filter_upwards [hfg,Lp.coeFn_sub g f] with x hx hs
    rw [hs]
    exact sub_nonneg.mpr hx
  have hh := hA (g-f) hsub
  rw [map_sub] at hh
  filter_upwards [hh,Lp.coeFn_sub (A g) (A f)] with x hx hs
  rw [hs] at hx
  exact sub_nonneg.mp hx

end HeatPositiveCone
#check @HeatPositiveCone.closed
#print axioms HeatPositiveCone.closed
#check @HeatPositiveCone.convex
#print axioms HeatPositiveCone.convex
#check @HeatPositiveCone.integral_nonnegative
#print axioms HeatPositiveCone.integral_nonnegative
#check @HeatPositiveCone.monotone
#print HeatPositiveCone.monotone
#print axioms HeatPositiveCone.monotone
