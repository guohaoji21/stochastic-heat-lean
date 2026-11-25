import HeatTorusMass
import HeatTorusPeriodicBarrier
import HeatTorusTensorGenerator
import HeatTorusGevreyCutoff
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace HeatTorusFixedBarrier

open MeasureTheory Set UnitAddTorus HeatTorusReal HeatTorusTensorGenerator HeatTorusMass
open scoped Topology NNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure := by
  change (AddCircle.haarAddCircle (T := 1)).IsAddHaarMeasure
  infer_instance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem second_add_nonneg (f f'' : ι → UnitAddCircle → ℝ) (A : ℝ)
    (hf : ∀ i x, 0 ≤ f i x) (hsub : ∀ i x, 0 ≤ f'' i x + A * f i x)
    (x : UnitAddTorus ι) :
    0 ≤ second f f'' x + ((Fintype.card ι : ℝ) * A) * tensor f x := by
  have h (i : ι) : 0 ≤ f'' i (x i) * (∏ j ∈ Finset.univ.erase i, f j (x j)) +
      A * tensor f x := by
    have hn : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j (x j) := Finset.prod_nonneg fun j _ => hf j _
    have ht : tensor f x = f i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j) :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
    rw [ht, ← mul_assoc, ← add_mul]
    exact mul_nonneg (hsub i _) hn
  have ho := Finset.sum_nonneg (s := (Finset.univ : Finset ι)) fun i _ => h i
  simpa only [second, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc] using ho

private theorem memLp_continuous (u : UnitAddTorus ι → ℝ) (hu : Continuous u) :
    MemLp u 2 volume :=
  hu.memLp_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

/-- A fixed continuous initial profile, positive at a point of the unit
plateau, dominates a nonzero (L^2) generator barrier. -/
theorem exists_barrier (P : ℝ) (b u : UnitAddTorus ι → ℝ) (hu : Continuous u)
    (hu₀ : ∀ x, 0 ≤ u x) (c : UnitAddTorus ι) (hc : u c = 1)
    (hplateau : ∀ x, u x ≠ 0 → b x = 1)
    (M : RealState ι →L[ℝ] RealState ι)
    (hM : ∀ v : RealState ι, (fun x => M v x) =ᵐ[volume] fun x => b x * v x)
    (U : RealState ι) (hU : (U : UnitAddTorus ι → ℝ) =ᵐ[volume] u) :
    ∃ (F G : RealState ι) (C : ℝ), 0 ≤ C ∧ F ≠ 0 ∧ M F = F ∧
      (∀ᵐ x ∂volume, 0 ≤ F x) ∧ (∀ᵐ x ∂volume, F x ≤ U x) ∧
      HasDerivWithinAt (fun s : ℝ => realHeat P s F) G (Ici 0) 0 ∧
      (∀ᵐ x ∂volume, 0 ≤ (G + C • F) x) := by
  let chart := HeatTorusGevreyCutoff.chart (P := 1) c
  have hpre : {x | (1 / 2 : ℝ) < u (chart x)} ∈ 𝓝 (0 : ι → ℝ) := by
    have hh : Continuous (u ∘ chart) := hu.comp (HeatTorusGevreyCutoff.continuous_chart c)
    have ht := hh.continuousAt (x := (0 : ι → ℝ))
    rw [ContinuousAt] at ht
    apply ht.eventually
    change Ioi (1 / 2 : ℝ) ∈ 𝓝 (u (chart 0))
    rw [show chart 0 = c from HeatTorusGevreyCutoff.chart_zero c, hc]
    exact Ioi_mem_nhds (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let R := min (1 / 4) (ε / 2)
  have hR : 0 < R := lt_min (by norm_num) (by positivity)
  have hsmall : R < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hRε : R < ε := (min_le_right _ _).trans_lt (by linarith)
  choose f f' f'' h using fun i : ι => HeatTorusPeriodicBarrier.exists_barrier hR hsmall (c i)
  have hf (i : ι) := (h i).1
  have hf' (i : ι) := (h i).2.1
  have hf'' (i : ι) := (h i).2.2.1
  have hd (i : ι) := (h i).2.2.2.1
  have hdd (i : ι) := (h i).2.2.2.2.1
  let A := 196 / (R - -R)^2
  have hb (i : ι) (x : UnitAddCircle) : 0 ≤ f i x ∧ f i x ≤ 1 ∧ 0 ≤ f'' i x + A * f i x :=
    (h i).2.2.2.2.2.1 x
  have htensor₀ (x : UnitAddTorus ι) : 0 ≤ tensor f x := Finset.prod_nonneg fun i _ => (hb i _).1
  have htensor₁ (x : UnitAddTorus ι) : tensor f x ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hb i _).1) (fun i _ => (hb i _).2.1)
  let W := tensor f
  let Z := fun x => P⁻¹ ^ 2 * second f f'' x
  have hW : Continuous W := continuous_tensor f hf
  have hZ : Continuous Z := continuous_const.mul (continuous_second f f'' hf hf'')
  let F₀ := (memLp_continuous W hW).toLp W
  let G₀ := (memLp_continuous Z hZ).toLp Z
  have hF₀ : (F₀ : UnitAddTorus ι → ℝ) =ᵐ[volume] W := (memLp_continuous W hW).coeFn_toLp
  have hG₀ : (G₀ : UnitAddTorus ι → ℝ) =ᵐ[volume] Z := (memLp_continuous Z hZ).coeFn_toLp
  let F := (1 / 2 : ℝ) • F₀
  let G := (1 / 2 : ℝ) • G₀
  let C : ℝ := P⁻¹ ^ 2 * ((Fintype.card ι : ℝ) * A)
  have hF : (F : UnitAddTorus ι → ℝ) =ᵐ[volume] fun x => (1 / 2 : ℝ) * W x := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) F₀, hF₀] with x hx hy
    change F x = (1 / 2 : ℝ) * W x
    rw [hx]
    simpa only [Pi.smul_apply, smul_eq_mul, hy]
  have hnear (x : UnitAddTorus ι) (hx : W x ≠ 0) : (1 / 2 : ℝ) < u x := by
    have hcoord (i : ι) : f i (x i) ≠ 0 := by
      intro hzero
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    choose y hy hy' using fun i : ι => (h i).2.2.2.2.2.2.2 (x i) (hcoord i)
    have hx' : chart y = x := by
      funext i
      exact (hy' i).symm
    have hdist : dist y 0 ≤ R := (dist_pi_le_iff hR.le).mpr fun i => by
      simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using (hy i).le
    have hyu := hball (hdist.trans_lt hRε)
    change (1 / 2 : ℝ) < u (chart y) at hyu
    rwa [hx'] at hyu
  have hWc : 0 < W c := Finset.prod_pos fun i _ => (h i).2.2.2.2.2.2.1
  have hFn : F ≠ 0 := by
    intro he
    have ha : (fun x => (1 / 2 : ℝ) * W x) =ᵐ[volume] (0 : UnitAddTorus ι → ℝ) := by
      rw [he] at hF
      exact hF.symm.trans (Lp.coeFn_zero ℝ 2 volume)
    have hh := (Continuous.ae_eq_iff_eq volume (continuous_const.mul hW)
      (continuous_const : Continuous (fun _ : UnitAddTorus ι => (0 : ℝ)))).mp ha
    have hz := congrFun hh c
    change (1 / 2 : ℝ) * W c = 0 at hz
    linarith
  refine ⟨F, G, C, by dsimp [C, A]; positivity, hFn, ?_, ?_, ?_, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [hM F, hF] with x hx hy
    rw [hx, hy]
    by_cases hw : W x = 0
    · simp [hw]
    · rw [hplateau x (ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 2).trans (hnear x hw))), one_mul]
  · filter_upwards [hF] with x hx
    rw [hx]
    exact mul_nonneg (by norm_num) (htensor₀ x)
  · filter_upwards [hF, hU] with x hx hu'
    rw [hx, hu']
    by_cases hw : W x = 0
    · simpa only [hw, mul_zero] using hu₀ x
    · exact (mul_le_of_le_one_right (by norm_num) (htensor₁ x)).trans (hnear x hw).le
  · have hd₀ := generator_tensor P f f' f'' hf hf' hf'' hd hdd F₀ G₀ hF₀ hG₀
    simpa only [F, G, map_smul, Pi.smul_def] using hd₀.const_smul (1 / 2 : ℝ)
  · filter_upwards [hF, hG₀, Lp.coeFn_smul (1 / 2 : ℝ) G₀,
      Lp.coeFn_add G (C • F), Lp.coeFn_smul C F] with x hx hz hg hsum hsm
    rw [hsum]
    change 0 ≤ G x + (C • F) x
    rw [hsm, hg]
    change 0 ≤ (1 / 2 : ℝ) * G₀ x + C * F x
    rw [hx, hz]
    have hp := second_add_nonneg f f'' A (fun i y => (hb i y).1) (fun i y => (hb i y).2.2) x
    have h := mul_nonneg (show 0 ≤ (1 / 2 : ℝ) * P⁻¹ ^ 2 by positivity) hp
    dsimp only [C, W, Z]
    convert h using 1
    ring

/-- For fixed data and final time, every time grid has the same positive
lower bound on the initial pairing. -/
theorem uniform_pairing (P : ℝ) (b u : UnitAddTorus ι → ℝ) (hu : Continuous u)
    (hu₀ : ∀ x, 0 ≤ u x) (c : UnitAddTorus ι) (hc : u c = 1)
    (hplateau : ∀ x, u x ≠ 0 → b x = 1)
    (M : RealState ι →L[ℝ] RealState ι) (hpos : Positive M)
    (hM : ∀ v : RealState ι, (fun x => M v x) =ᵐ[volume] fun x => b x * v x)
    (U : RealState ι) (hU : (U : UnitAddTorus ι → ℝ) =ᵐ[volume] u) (T : ℝ≥0) :
    ∃ a : ℝ, 0 < a ∧ ∀ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t → t 0 = 0 → t N = T →
      a ≤ inner ℝ U (HeatBackwardChain.stateAt (HeatTorusCovarianceSeparation.K P M)
        (fun j => t j - t (j - 1)) N U 0) := by
  obtain ⟨f, g, C, _, hf, hfix, hfn, hfu, hg, hsub⟩ :=
    exists_barrier P b u hu hu₀ c hc hplateau M hM U hU
  refine ⟨Real.exp (-C * (T : ℝ)) * ‖f‖ ^ 2,
    mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.mpr hf) 2), ?_⟩
  intro t N ht h0 hN
  have h := pairing_lower P C M hpos f g U hfix hg hsub hfn hfu t ht h0 N
  rwa [hN] at h

end HeatTorusFixedBarrier

#print axioms HeatTorusFixedBarrier.exists_barrier
#print axioms HeatTorusFixedBarrier.uniform_pairing
