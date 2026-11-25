import HeatGevreyRealTaylor
import HeatTorusGevreyCutoff

set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace HeatGevreyOneUniqueness

open Filter Set HeatGevreyProduct
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem iteratedDeriv_section (i : ι) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u => f (Function.update x i u)) t =
      mixedPartial (List.replicate n i) f (Function.update x i t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, List.replicate_succ, mixedPartial, coordinateDeriv, Function.update_self]
    congr 1
    funext u
    rw [ih, Function.update_idem]

/-- A real Gevrey-1 function with the paper's mixed derivative bound cannot
vanish on an open neighborhood unless it vanishes everywhere. -/
theorem eq_zero_of_local_zero (f : (ι → ℝ) → ℝ) (C ρ : ℝ) (hρ : 0 < ρ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hD : ∀ (l : List ι) x, |mixedPartial l f x| ≤ C * ρ ^ l.length * (l.length.factorial : ℝ))
    (c : ι → ℝ) (hc : ∀ᶠ x in 𝓝 c, f x = 0) : f = 0 := by
  obtain ⟨ε, hε, hbox⟩ := Metric.mem_nhds_iff.mp hc
  have h (s : Finset ι) : ∀ x : ι → ℝ, (∀ i ∉ s, |x i - c i| < ε) → f x = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      apply hbox
      exact (dist_pi_lt_iff hε).mpr fun i => by
        simpa only [Real.dist_eq] using hx i (Finset.notMem_empty i)
    | @insert i s hi ih =>
      intro x hx
      let sectionFun := fun t : ℝ => f (Function.update x i t)
      have hu : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Function.update x i t) := by
        apply contDiff_pi.mpr
        intro j
        by_cases hj : j = i
        · subst j
          have he : (fun t : ℝ => Function.update x i t i) = id := by
            funext t
            exact Function.update_self i t x
          rw [he]
          exact contDiff_id
        · simpa only [Function.update_of_ne hj] using
            (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => x j))
      have hd (n : ℕ) (t : ℝ) : |iteratedDeriv n sectionFun t| ≤ C * ρ^n * (n.factorial : ℝ) := by
        change |iteratedDeriv n (fun u => f (Function.update x i u)) t| ≤ _
        rw [iteratedDeriv_section]
        simpa only [List.length_replicate] using hD (List.replicate n i) (Function.update x i t)
      have hl : sectionFun =ᶠ[𝓝 (c i)] 0 := by
        filter_upwards [Metric.ball_mem_nhds (c i) hε] with t ht
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self, Metric.mem_ball, Real.dist_eq] using ht
        · rw [Function.update_of_ne hji]
          exact hx j (by simp [hji, hj])
      have he := HeatGevreyRealTaylor.eq_zero_of_flat sectionFun C ρ hρ (hf.comp hu) hd (c i)
        (fun n => by simpa using (hl.iteratedDeriv n).eq_of_nhds)
      have hh := congrFun he (x i)
      simpa only [sectionFun, Function.update_eq_self, Pi.zero_apply] using hh
  funext x
  exact h Finset.univ x fun i hi => (hi (Finset.mem_univ i)).elim

theorem periodic_eq_zero_of_local_zero {P : ℝ} (b : (ι → AddCircle P) → ℝ) (C ρ : ℝ)
    (hρ : 0 < ρ) (hf : ContDiff ℝ (⊤ : ℕ∞) (b ∘ HeatTorusGevreyCutoff.chart 0))
    (hD : ∀ (l : List ι) x, |mixedPartial l (b ∘ HeatTorusGevreyCutoff.chart 0) x| ≤
      C * ρ ^ l.length * (l.length.factorial : ℝ))
    (c : ι → AddCircle P) (hc : ∀ᶠ x in 𝓝 c, b x = 0) : b = 0 := by
  let q := HeatTorusGevreyCutoff.chart (P := P) (0 : ι → AddCircle P)
  have hsurj : Function.Surjective q := by
    intro x
    choose y hy using fun i : ι =>
      (QuotientAddGroup.mk_surjective : Function.Surjective (fun u : ℝ => (u : AddCircle P))) (x i)
    refine ⟨y, ?_⟩
    simpa only [q, HeatTorusGevreyCutoff.chart, zero_add] using funext hy
  obtain ⟨x, hx⟩ := hsurj c
  have hq : Continuous q := HeatTorusGevreyCutoff.continuous_chart _
  have hloc : ∀ᶠ y in 𝓝 x, (b ∘ q) y = 0 := by
    have ht := hq.continuousAt (x := x)
    rw [ContinuousAt, hx] at ht
    exact ht.eventually hc
  have hzero := eq_zero_of_local_zero (b ∘ q) C ρ hρ hf hD x hloc
  funext c'
  obtain ⟨y, rfl⟩ := hsurj c'
  exact congrFun hzero y

end HeatGevreyOneUniqueness

#print axioms HeatGevreyOneUniqueness.eq_zero_of_local_zero
#print axioms HeatGevreyOneUniqueness.periodic_eq_zero_of_local_zero
