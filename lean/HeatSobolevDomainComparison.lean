import HeatSobolevIntervalMaps
import HeatSobolevPositivePart

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HeatSobolevDomainComparison

open EllipticPdes EllipticPdes.H1Graph Filter MeasureTheory Set
open HeatSobolevIntervalMaps HeatSobolevPositivePart
open scoped RealInnerProductSpace

/-- Comparison of the variational solutions on nested open intervals of the
real line. The equations have the same restricted datum and zeroth-order term. -/
theorem extend_le_of_variational {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J) (hJI : J ⊆ I)
    {a : ℝ} (ha : 0 < a) (f : State I) (U : H01 volume J) (V : H01 volume I)
    (hV : ∀ᵐ x ∂volume.restrict I, 0 ≤ fnL (V : Graph I) x)
    (hUeq : ∀ W : H01 volume J,
      a * inner ℝ (fnL (U : Graph J)) (fnL (W : Graph J)) +
        inner ℝ (gradL (U : Graph J)) (gradL (W : Graph J)) =
      inner ℝ (restrictL2 hJI f) (fnL (W : Graph J)))
    (hVeq : ∀ W : H01 volume I,
      a * inner ℝ (fnL (V : Graph I)) (fnL (W : Graph I)) +
        inner ℝ (gradL (V : Graph I)) (gradL (W : Graph I)) =
      inner ℝ f (fnL (W : Graph I))) :
    ∀ᵐ x ∂volume.restrict I, extendL2 hJI (fnL (U : Graph J)) x ≤ fnL (V : Graph I) x := by
  let Y := restrictGraph hJI (V : Graph I)
  let X := (U : Graph J) - Y
  let W := positivePart X
  have hWfn := fnL_positivePart X
  have hWgrad := gradL_positivePart X
  have hYrep : ⇑(fnL Y) =ᵐ[volume.restrict J] fnL (V : Graph I) := restrictL2_ae hJI _
  have hXrep : ∀ᵐ x ∂volume.restrict J, fnL X x = fnL (U : Graph J) x - fnL Y x := by
    dsimp only [X]
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (fnL (U : Graph J)) (fnL Y)] with x hx
    simpa only [Pi.sub_apply] using hx
  have hYpos : ∀ᵐ x ∂volume.restrict J, 0 ≤ fnL Y x := by
    filter_upwards [hYrep, hV.filter_mono (ae_mono (Measure.restrict_mono hJI le_rfl))]
      with x hx hp
    rwa [hx]
  have hWnonneg : ∀ᵐ x ∂volume.restrict J, 0 ≤ fnL W x :=
    hWfn.mono fun _ hx => by rw [hx]; exact le_max_right _ _
  have hWle : ∀ᵐ x ∂volume.restrict J, fnL W x ≤ fnL (positivePart (U : Graph J)) x := by
    filter_upwards [hWfn, hXrep, hYpos, fnL_positivePart (U : Graph J)] with x hw hx hpos hu
    rw [hw, hx, hu]
    exact max_le_max (sub_le_self _ hpos) le_rfl
  have hX : X ∈ W12 volume J := (W12 volume J).sub_mem (H01_le_W12 U.property)
    (restrictGraph_mem_W12 hI hJ hJI (H01_le_W12 V.property))
  have hUp : positivePart (U : Graph J) ∈ H01 volume J := by
    obtain ⟨Z, hZ, hf, hg⟩ := exists_mem_H01_posPart_sub_const hJ U.property (le_refl (0 : ℝ))
    have hEq : Z = positivePart (U : Graph J) := H1Graph.ext
      (Lp.ext ((by simpa only [sub_zero] using hf : ⇑(fnL Z) =ᵐ[volume.restrict J]
        fun x => max (fnL (U : Graph J) x) 0).trans (fnL_positivePart _).symm))
      (Lp.ext (hg.trans (gradL_positivePart _).symm))
    rwa [hEq] at hZ
  have hW : W ∈ H01 volume J := mem_H01_of_nonnegative_le hJ hUp
    (positivePart_mem_W12 hJ hX) hWnonneg hWle
  let WJ : H01 volume J := ⟨W, hW⟩
  let WI : H01 volume I := ⟨extendGraph hJI W, extendGraph_mem_H01 hJ.measurableSet hJI hW⟩
  have hVe := hVeq WI
  change a * inner ℝ (fnL (V : Graph I)) (extendL2 hJI (fnL W)) +
      inner ℝ (gradL (V : Graph I)) (extendL2 hJI (gradL W)) =
      inner ℝ f (extendL2 hJI (fnL W)) at hVe
  simp only [extendL2, ContinuousLinearMap.adjoint_inner_right] at hVe
  have hVeq' : a * inner ℝ (fnL Y) (fnL W) + inner ℝ (gradL Y) (gradL W) =
      inner ℝ (restrictL2 hJI f) (fnL W) := hVe
  have hUe := hUeq WJ
  change a * inner ℝ (fnL (U : Graph J)) (fnL W) +
    inner ℝ (gradL (U : Graph J)) (gradL W) = _ at hUe
  have henergy : a * inner ℝ (fnL X) (fnL W) + inner ℝ (gradL X) (gradL W) = 0 := by
    dsimp only [X]
    simp only [map_sub, inner_sub_left]
    linarith only [hUe, hVeq']
  have hfirst : inner ℝ (fnL X) (fnL W) = ‖fnL W‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWfn] with x hx
    rw [Real.inner_apply, Real.inner_apply]
    rw [show fnL W x = max (fnL X x) 0 from hx]
    by_cases hx0 : 0 ≤ fnL X x
    · rw [max_eq_left hx0]
    · simp [max_eq_right (le_of_not_ge hx0)]
  have hsecond : inner ℝ (gradL X) (gradL W) = ‖gradL W‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWgrad] with x hx
    rw [Real.inner_apply, Real.inner_apply, show gradL W x = _ from hx]
    split_ifs <;> simp
  rw [hfirst, hsecond] at henergy
  have hnorm : ‖fnL W‖ = 0 := by
    have hsq : ‖fnL W‖ ^ 2 = 0 := by
      apply le_antisymm _ (sq_nonneg _)
      apply nonpos_of_mul_nonpos_left _ ha
      linarith only [henergy, sq_nonneg ‖gradL W‖]
    simpa using hsq
  have hwzero := norm_eq_zero.mp hnorm
  have hXle : ∀ᵐ x ∂volume.restrict J, fnL (U : Graph J) x ≤ fnL (V : Graph I) x := by
    have hw : ⇑(fnL W) =ᵐ[volume.restrict J] 0 := by
      rw [hwzero]
      exact Lp.coeFn_zero ℝ 2 (volume.restrict J)
    filter_upwards [hYrep, hXrep, hWfn, hw] with x hy hx hp hz
    have hle := le_max_left (fnL X x) (0 : ℝ)
    rw [← hp, hz, hx, hy] at hle
    exact sub_nonpos.mp hle
  filter_upwards [hV, (ae_restrict_iff' hJ.measurableSet).mp
    (hXle.filter_mono (ae_mono (le_of_eq (nestedMeasure hJI)))),
    extendL2_ae hJI hJ.measurableSet (fnL (U : Graph J))] with x hv hx he
  rw [he]
  by_cases hjx : x ∈ J
  · rw [indicator_of_mem hjx]
    exact hx hjx
  · rwa [indicator_of_notMem hjx]

end HeatSobolevDomainComparison

#print axioms HeatSobolevDomainComparison.extend_le_of_variational
