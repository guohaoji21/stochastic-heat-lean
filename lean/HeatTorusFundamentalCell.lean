import HeatFlatTorusSmoothLift
import HeatTorusReal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HeatTorusFundamentalCell

open MeasureTheory Filter Set UnitAddTorus HeatFlatTorusSmoothLift

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

/-- The half-open fundamental cell in normalized Euclidean coordinates. -/
def cell (a : ι → ℝ) : Set (EuclideanSpace ℝ ι) :=
  WithLp.ofLp ⁻¹' (univ : Set ι).pi (fun i => Ioc (a i) (a i + 1))

theorem cell_measurePreserving (a : ι → ℝ) :
    MeasurePreserving (covering 1 : EuclideanSpace ℝ ι → UnitAddTorus ι)
      (volume.restrict (cell a)) volume := by
  let B := (univ : Set ι).pi (fun i => Ioc (a i) (a i + 1))
  have hB : MeasurableSet B := MeasurableSet.pi (to_countable _) (fun _ _ => measurableSet_Ioc)
  have h₁ : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ))
      (volume.restrict (cell a)) (volume.restrict B) :=
    (PiLp.volume_preserving_ofLp (ι := ι)).restrict_preimage hB
  have h₂ : MeasurePreserving (fun (x : ι → ℝ) i => (x i : UnitAddCircle))
      (volume.restrict B) volume := by
    have h := measurePreserving_pi _ _ (fun i => UnitAddCircle.measurePreserving_mk (a i))
    rw [← Measure.restrict_pi_pi] at h
    convert h using 1
    simp [volume, AddCircle.haarAddCircle]
  exact h₂.comp h₁

omit [Fintype ι] in
theorem injOn_cell (a : ι → ℝ) : (cell a).InjOn (covering 1) := by
  intro x hx y hy he
  apply PiLp.ext
  intro i
  have hxi : x i ∈ Ioc (a i) (a i + 1) := hx i (mem_univ i)
  have hyi : y i ∈ Ioc (a i) (a i + 1) := hy i (mem_univ i)
  have hi : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun he i
  have h := congrArg (fun z => (AddCircle.equivIoc 1 (a i) z).val) hi
  simpa only [AddCircle.equivIoc_coe_eq hxi, AddCircle.equivIoc_coe_eq hyi] using h

/-- Lebesgue measure on any measurable patch inside one cell is carried to
the restricted Haar measure on its image in the normalized torus. -/
theorem patch_measurePreserving (a : ι → ℝ) {U : Set (EuclideanSpace ℝ ι)}
    (hU : U ⊆ cell a) (hm : MeasurableSet (covering 1 '' U)) :
    MeasurePreserving (covering 1 : EuclideanSpace ℝ ι → UnitAddTorus ι)
      (volume.restrict U) (volume.restrict (covering 1 '' U)) := by
  have he : (covering 1 ⁻¹' (covering 1 '' U)) ∩ cell a = U := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, he⟩, hx⟩
      have h := injOn_cell a (hU hy) hx he
      rwa [← h]
    · intro hx
      exact ⟨mem_image_of_mem (covering 1) hx, hU hx⟩
  have h := (cell_measurePreserving a).restrict_preimage hm
  rw [Measure.restrict_restrict ((cell_measurePreserving a).measurable hm), he] at h
  exact h

/-- Pullback identifies the (L²) norm on a torus patch with the Euclidean
(L²) norm in its fundamental-cell coordinates. -/
def patchPullback (a : ι → ℝ) {U : Set (EuclideanSpace ℝ ι)}
    (hU : U ⊆ cell a) (hm : MeasurableSet (covering 1 '' U)) :
    Lp ℝ 2 (volume.restrict (covering 1 '' U)) →ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict U) :=
  Lp.compMeasurePreservingₗᵢ ℝ (covering 1) (patch_measurePreserving a hU hm)

/-- The unique representative in the half-open Euclidean cell. -/
def representative (a : ι → ℝ) (x : UnitAddTorus ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (measurableEquivPiIoc a x).1

omit [Fintype ι] in
theorem representative_mem (a : ι → ℝ) (x : UnitAddTorus ι) :
    representative a x ∈ cell a :=
  fun i _ => (measurableEquivPiIoc a x).2 i

omit [Fintype ι] in
theorem covering_representative (a : ι → ℝ) (x : UnitAddTorus ι) :
    covering 1 (representative a x) = x :=
  (measurableEquivPiIoc a).symm_apply_apply x

omit [Fintype ι] in
theorem representative_covering (a : ι → ℝ) {x : EuclideanSpace ℝ ι} (hx : x ∈ cell a) :
    representative a (covering 1 x) = x :=
  injOn_cell a (representative_mem a _) hx (covering_representative a _)

theorem measurable_representative (a : ι → ℝ) : Measurable (representative a) :=
  (PiLp.volume_preserving_toLp (ι := ι)).measurable.comp
    (measurable_subtype_coe.comp (measurableEquivPiIoc a).measurable)

theorem representative_measurePreserving (a : ι → ℝ) {U : Set (EuclideanSpace ℝ ι)}
    (hU : U ⊆ cell a) (hUm : MeasurableSet U) (hm : MeasurableSet (covering 1 '' U)) :
    MeasurePreserving (representative a) (volume.restrict (covering 1 '' U)) (volume.restrict U) := by
  have hc := patch_measurePreserving a hU hm
  refine ⟨measurable_representative a, ?_⟩
  rw [← hc.map_eq, Measure.map_map (measurable_representative a) hc.measurable]
  calc
    _ = Measure.map id (volume.restrict U) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hUm] with x hx
      exact representative_covering a (hU hx)
    _ = _ := Measure.map_id

/-- The Euclidean and torus (L²) spaces on an embedded patch are
surjectively isometric, by pullback and the cell representative. -/
def patchEquiv (a : ι → ℝ) {U : Set (EuclideanSpace ℝ ι)}
    (hU : U ⊆ cell a) (hUm : MeasurableSet U) (hm : MeasurableSet (covering 1 '' U)) :
    Lp ℝ 2 (volume.restrict (covering 1 '' U)) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict U) :=
  LinearIsometryEquiv.ofSurjective (patchPullback a hU hm) fun f => by
    let hc := patch_measurePreserving a hU hm
    let hr := representative_measurePreserving a hU hUm hm
    let g := Lp.compMeasurePreserving (representative a) hr f
    refine ⟨g, Lp.ext ?_⟩
    change (Lp.compMeasurePreserving (covering 1) hc g : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict U] f
    filter_upwards [Lp.coeFn_compMeasurePreserving g hc,
      hc.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hr), ae_restrict_mem hUm]
      with x hx hy hz
    exact hx.trans (hy.trans (congrArg f (representative_covering a (hU hz))))

theorem closedBall_subset_cell (c : EuclideanSpace ℝ ι) {r : ℝ} (hr : r < 1 / 2) :
    Metric.closedBall c r ⊆ cell (fun i => c i - 1 / 2) := by
  intro x hx i _
  have hi := (PiLp.dist_apply_le x c i).trans (Metric.mem_closedBall.mp hx)
  rw [Real.dist_eq] at hi
  have hi' := abs_le.mp hi
  exact ⟨by linarith [hi'.1], by linarith [hi'.2]⟩

end HeatTorusFundamentalCell

#print axioms HeatTorusFundamentalCell.cell_measurePreserving
#print axioms HeatTorusFundamentalCell.injOn_cell
#print axioms HeatTorusFundamentalCell.patch_measurePreserving
#print axioms HeatTorusFundamentalCell.patchPullback
#print axioms HeatTorusFundamentalCell.patchEquiv
#print axioms HeatTorusFundamentalCell.closedBall_subset_cell
