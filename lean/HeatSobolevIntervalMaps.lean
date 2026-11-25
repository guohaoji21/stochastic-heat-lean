import HeatRestrictionAdjoint
import EllipticPdes.Sobolev.GraphLattice

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HeatSobolevIntervalMaps

open EllipticPdes EllipticPdes.H1Graph Filter MeasureTheory Set
open scoped ENNReal Topology

abbrev State (I : Set ℝ) := Lp ℝ 2 (volume.restrict I)
abbrev Graph (I : Set ℝ) := H1Graph (volume : Measure ℝ) I

/-- Act on the function and spatial derivative components of the real graph. -/
def mapGraph {I J : Set ℝ} (f g : State I →L[ℝ] State J) : Graph I →L[ℝ] Graph J where
  toFun U := H1Graph.mk (f (fnL U)) (g (gradL U))
  map_add' U V := by
    apply H1Graph.ext <;> simp
  map_smul' c U := by
    apply H1Graph.ext <;> simp
  cont := WithLp.prod_continuous_toLp .. |>.comp
    ((f.continuous.comp fnL.continuous).prodMk (g.continuous.comp gradL.continuous))

@[simp] theorem fnL_mapGraph {I J : Set ℝ} (f g : State I →L[ℝ] State J) (U : Graph I) :
    fnL (mapGraph f g U) = f (fnL U) := rfl

@[simp] theorem gradL_mapGraph {I J : Set ℝ} (f g : State I →L[ℝ] State J) (U : Graph I) :
    gradL (mapGraph f g U) = g (gradL U) := rfl

theorem nestedMeasure {I J : Set ℝ} (hJI : J ⊆ I) : (volume.restrict I).restrict J =
    (volume : Measure ℝ).restrict J := Measure.restrict_restrict_of_subset hJI

private theorem restrict_le_one {I J : Set ℝ} (hJI : J ⊆ I) :
    (volume : Measure ℝ).restrict J ≤ (1 : ℝ≥0∞) • volume.restrict I := by
  simpa only [one_smul] using Measure.restrict_mono hJI (le_refl (volume : Measure ℝ))

def restrictL2 {I J : Set ℝ} (hJI : J ⊆ I) : State I →L[ℝ] State J :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (restrict_le_one hJI)

theorem restrictL2_ae {I J : Set ℝ} (hJI : J ⊆ I) (f : State I) :
    (restrictL2 hJI f : ℝ → ℝ) =ᵐ[volume.restrict J] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top (restrict_le_one hJI) f

def extendL2 {I J : Set ℝ} (hJI : J ⊆ I) : State J →L[ℝ] State I := (restrictL2 hJI).adjoint

theorem extendL2_ae {I J : Set ℝ} (hJI : J ⊆ I) (hJ : MeasurableSet J) (f : State J) :
    (extendL2 hJI f : ℝ → ℝ) =ᵐ[volume.restrict I] J.indicator f := by
  let μ := (volume : Measure ℝ).restrict I
  have hmem : MemLp (J.indicator f) 2 μ := (memLp_indicator_iff_restrict hJ.nullMeasurableSet).2
    ((Lp.memLp f).mono_measure (le_of_eq (nestedMeasure hJI)))
  have he : extendL2 hJI f = hmem.toLp _ := by
    apply ext_inner_left ℝ
    intro w
    rw [extendL2, ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
    have hchange (F : ℝ → ℝ) : (∫ x, F x ∂volume.restrict J) = ∫ x, J.indicator F x ∂μ := by
      rw [integral_indicator hJ, nestedMeasure hJI]
    rw [hchange]
    apply integral_congr_ae
    have hr : ∀ᵐ x ∂μ, x ∈ J → restrictL2 hJI w x = w x := by
      exact (ae_restrict_iff' hJ).mp ((restrictL2_ae hJI w).filter_mono
        (ae_mono (le_of_eq (nestedMeasure hJI))))
    filter_upwards [hr, hmem.coeFn_toLp] with x hx hw
    by_cases hm : x ∈ J
    · rw [indicator_of_mem hm, hw, indicator_of_mem hm, hx hm]
    · rw [indicator_of_notMem hm, hw, indicator_of_notMem hm]
      simp
  rw [he]
  exact hmem.coeFn_toLp

def restrictGraph {I J : Set ℝ} (hJI : J ⊆ I) : Graph I →L[ℝ] Graph J :=
  mapGraph (restrictL2 hJI) (restrictL2 hJI)

def extendGraph {I J : Set ℝ} (hJI : J ⊆ I) : Graph J →L[ℝ] Graph I :=
  mapGraph (extendL2 hJI) (extendL2 hJI)

theorem restrictGraph_mem_W12 {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J) (hJI : J ⊆ I)
    {U : Graph I} (hU : U ∈ W12 volume I) : restrictGraph hJI U ∈ W12 volume J := by
  rw [mem_W12_iff_hasWeakFDerivOn hJ]
  refine (((mem_W12_iff_hasWeakFDerivOn hI U).mp hU).mono hJI).congr_ae ?_ ?_
  · exact (restrictL2_ae hJI (fnL U)).symm
  · exact (restrictL2_ae hJI (gradL U)).symm.mono (fun _ h => congrArg (innerSL ℝ) h)

theorem extendGraph_mem_H01 {I J : Set ℝ} (hJ : MeasurableSet J) (hJI : J ⊆ I)
    {U : Graph J} (hU : U ∈ H01 volume J) : extendGraph hJI U ∈ H01 volume I := by
  obtain ⟨φ, hφ⟩ := exists_seq_testGraphₗ_tendsto hU
  refine isClosed_H01.mem_of_tendsto ((extendGraph hJI).continuous.continuousAt.tendsto.comp hφ)
    (Eventually.of_forall fun n => ?_)
  let ψ : testFunctions I := ⟨φ n, (φ n).2.1, (φ n).2.2.1, (φ n).2.2.2.trans hJI⟩
  have hfn : (fnL (extendGraph hJI (testGraphₗ volume J (φ n))) : ℝ → ℝ) =ᵐ[volume.restrict I] ψ := by
    rw [extendGraph, fnL_mapGraph]
    have hr := (ae_restrict_iff' (μ := volume.restrict I) hJ).mp
      ((coeFn_fnL_testGraphₗ (φ n)).filter_mono (ae_mono (le_of_eq (nestedMeasure hJI))))
    filter_upwards [extendL2_ae hJI hJ (fnL (testGraphₗ volume J (φ n))), hr] with x hx hy
    by_cases hm : x ∈ J
    · rw [hx, indicator_of_mem hm, hy hm]
    · rw [hx, indicator_of_notMem hm]
      exact (image_eq_zero_of_notMem_tsupport (fun hs => hm ((φ n).2.2.2 hs))).symm
  have hgrad : (gradL (extendGraph hJI (testGraphₗ volume J (φ n))) : ℝ → ℝ) =ᵐ[volume.restrict I]
      gradient (ψ : ℝ → ℝ) := by
    rw [extendGraph, gradL_mapGraph]
    have hr := (ae_restrict_iff' (μ := volume.restrict I) hJ).mp
      ((coeFn_gradL_testGraphₗ (φ n)).filter_mono (ae_mono (le_of_eq (nestedMeasure hJI))))
    filter_upwards [extendL2_ae hJI hJ (gradL (testGraphₗ volume J (φ n))), hr] with x hx hy
    by_cases hm : x ∈ J
    · rw [hx, indicator_of_mem hm, hy hm]
    · rw [hx, indicator_of_notMem hm]
      exact (gradient_eq_deriv'.trans
        (deriv_of_notMem_tsupport (fun hs => hm ((φ n).2.2.2 hs)))).symm
  have he : extendGraph hJI (testGraphₗ volume J (φ n)) = testGraphₗ volume I ψ :=
    H1Graph.ext (Lp.ext (hfn.trans (coeFn_fnL_testGraphₗ ψ).symm))
      (Lp.ext (hgrad.trans (coeFn_gradL_testGraphₗ ψ).symm))
  rw [Function.comp_apply, he]
  exact testGraphₗ_mem_H01 ψ

end HeatSobolevIntervalMaps

#print axioms HeatSobolevIntervalMaps.restrictGraph_mem_W12
#print axioms HeatSobolevIntervalMaps.extendGraph_mem_H01
