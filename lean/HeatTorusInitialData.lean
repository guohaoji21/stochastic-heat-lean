import HeatTorusGevreyCutoff
import HeatTorusReal
import HeatScalarMultiplier
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
noncomputable section

namespace HeatTorusInitialData

open MeasureTheory Set UnitAddTorus HeatTorusReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure := by
  change (AddCircle.haarAddCircle (T := 1)).IsAddHaarMeasure
  infer_instance

variable {ι : Type*} {P : ℝ}

/-- Coordinate rescaling into the physical torus from the unit torus
used in the Fourier `L²` implementation. -/
def rescale (hP : 0 < P) : UnitAddTorus ι ≃ₜ (ι → AddCircle P) :=
  Homeomorph.piCongrRight (fun _ => AddCircle.homeomorphAddCircle (1 : ℝ) P one_ne_zero hP.ne')

theorem rescale_coe (hP : 0 < P) (x : ι → ℝ) (i : ι) :
    rescale hP (fun j => (x j : UnitAddCircle)) i = ((x i * P : ℝ) : AddCircle P) := by
  change AddCircle.homeomorphAddCircle (1 : ℝ) P one_ne_zero hP.ne' (x i : UnitAddCircle) = _
  simp

variable [Fintype ι]

/-- The physical functions give a contractive noise multiplier and a
nonzero initial vector fixed by multiplication by that coefficient. -/
theorem exists_multiplier_and_initial (hP : 0 < P) (b g : (ι → AddCircle P) → ℝ)
    (hb : Continuous b) (hg : Continuous g) (h01 : ∀ x, b x ∈ Set.Icc 0 1)
    (c : ι → AddCircle P) (hc : g c = 1) (hplateau : ∀ x ∈ tsupport g, b x = 1) :
    ∃ (M : RealState ι →L[ℝ] RealState ι) (G : RealState ι),
      ‖M‖ ≤ 1 ∧ G ≠ 0 ∧ M G = G ∧
      (G : UnitAddTorus ι → ℝ) =ᵐ[volume] g ∘ rescale hP ∧
      (∀ᵐ x : UnitAddTorus ι ∂volume, rescale hP x ∉ tsupport g → G x = 0) ∧
      ∀ v : RealState ι, (fun x => M v x) =ᵐ[volume] fun x => b (rescale hP x) * v x := by
  let b₀ := b ∘ (rescale (ι := ι) hP)
  let g₀ := g ∘ (rescale (ι := ι) hP)
  have hb₀ : Continuous b₀ := hb.comp (rescale hP).continuous
  have hg₀ : Continuous g₀ := hg.comp (rescale hP).continuous
  have hbound : ∀ᵐ x : UnitAddTorus ι ∂volume, ‖b₀ x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    change ‖b (rescale hP x)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]
    exact (h01 _).2
  have hgc : HasCompactSupport g₀ := isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have hmem : MemLp g₀ 2 volume := hg₀.memLp_of_hasCompactSupport hgc
  let G := hmem.toLp g₀
  have hG : (G : UnitAddTorus ι → ℝ) =ᵐ[volume] g₀ := hmem.coeFn_toLp
  have hG_ne : G ≠ 0 := by
    intro he
    have hzero : g₀ =ᵐ[(volume : Measure (UnitAddTorus ι))] (0 : UnitAddTorus ι → ℝ) := by
      rw [he] at hG
      exact hG.symm.trans (Lp.coeFn_zero ℝ 2 volume)
    have hfun := (Continuous.ae_eq_iff_eq volume hg₀
      (continuous_const : Continuous (fun _ : UnitAddTorus ι => (0 : ℝ)))).mp hzero
    have h := congrFun hfun ((rescale hP).symm c)
    simpa [g₀, hc] using h
  obtain ⟨M, hM, happly⟩ := HeatScalarMultiplier.exists_multiplier volume b₀ hb₀.aestronglyMeasurable hbound
  refine ⟨M, G, hM, hG_ne, ?_, hG, ?_, happly⟩
  · apply Lp.ext
    filter_upwards [happly G, hG] with x hx hgx
    rw [hx, hgx]
    by_cases hzero : g₀ x = 0
    · rw [hzero, mul_zero]
    · have hone : b₀ x = 1 := hplateau _ (subset_tsupport g hzero)
      rw [hone, one_mul]
  · filter_upwards [hG] with x hx hxS
    have hz : g (rescale hP x) = 0 := image_eq_zero_of_notMem_tsupport hxS
    exact hx.trans hz

variable [DecidableEq ι]

/-- The data for the periodic obstruction, including the multiplier and its
nonzero fixed vector in the same `L²` space as the Fourier semigroup. -/
theorem exists_data_in_gap (hP : 0 < P) {s : ℝ} (hs : 1 < s)
    {U G₀ : Set (ι → AddCircle P)} (hU : IsOpen U) (hdisj : Disjoint U G₀)
    (c : ι → AddCircle P) (hc : c ∈ U) :
    ∃ (b g : (ι → AddCircle P) → ℝ) (ρ : ℝ)
      (M : RealState ι →L[ℝ] RealState ι) (G : RealState ι),
      0 < ρ ∧ ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0) ∧
      (∀ (l : List ι) x, ‖HeatGevreyProduct.mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x‖ ≤
        ρ ^ l.length * (l.length.factorial : ℝ) ^ s) ∧
      ContDiff ℝ (⊤ : ℕ∞) (g ∘ HeatTorusGevreyCutoff.chart 0) ∧
      tsupport b ⊆ U ∧ (∀ x ∈ tsupport g, b x = 1) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport b, ∀ y ∈ G₀, δ < dist x y) ∧
      ‖M‖ ≤ 1 ∧ G ≠ 0 ∧ M G = G ∧
      (G : UnitAddTorus ι → ℝ) =ᵐ[volume] g ∘ rescale hP ∧
      (∀ᵐ x : UnitAddTorus ι ∂volume, 0 ≤ G x) ∧
      (∀ᵐ x : UnitAddTorus ι ∂volume, rescale hP x ∉ U → G x = 0) ∧
      ∀ v : RealState ι, (fun x => M v x) =ᵐ[volume] fun x => b (rescale hP x) * v x := by
  obtain ⟨b, g, ρ, hρ, hb, hg, hbreg, hbgev, hb01, hg01, _, _, hgreg, hg1, hb1, hgU, hbU, hδ⟩ :=
    HeatTorusGevreyCutoff.exists_cutoff_and_initial hP hs hU hdisj c hc
  obtain ⟨M, G, hM, hGne, hMG, hG, hGS, hMv⟩ :=
    exists_multiplier_and_initial hP b g hb hg hb01 c hg1 hb1
  refine ⟨b, g, ρ, M, G, hρ, hbreg, hbgev, hgreg, hbU, hb1, hδ, hM, hGne,
    hMG, hG, ?_, ?_, hMv⟩
  · filter_upwards [hG] with x hx
    exact hx.symm ▸ (hg01 _).1
  · filter_upwards [hGS] with x hx hU
    exact hx (fun hS => hU (hgU hS))

end HeatTorusInitialData

#print axioms HeatTorusInitialData.exists_multiplier_and_initial
#print axioms HeatTorusInitialData.exists_data_in_gap
