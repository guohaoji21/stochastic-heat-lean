import HeatGevreyCutoff
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Finsupp.Multiset

set_option autoImplicit false
noncomputable section

namespace HeatGevreyProduct

open Finset Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A directional derivative along one of the coordinate axes. -/
def coordinateDeriv (i : ι) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  deriv (fun t => f (Function.update x i t)) (x i)

/-- A list records the order of differentiation and the number of times
each coordinate is used. This represents every mixed multi-index. -/
def mixedPartial : List ι → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], f => f
  | i :: l, f => coordinateDeriv i (mixedPartial l f)

def product (g : ι → ℝ → ℝ) (x : ι → ℝ) : ℝ := ∏ i, g i (x i)

omit [DecidableEq ι] in
theorem contDiff_product (g : ι → ℝ → ℝ) (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) :
    ContDiff ℝ (⊤ : ℕ∞) (product g) :=
  contDiff_prod (fun i _ => (hg i).comp (contDiff_apply ℝ (fun _ => ℝ) i))

theorem partial_product (g : ι → ℝ → ℝ) (i : ι) (x : ι → ℝ) :
    coordinateDeriv i (product g) x = ∏ j, (if j = i then deriv (g j) (x j) else g j (x j)) := by
  have hi : i ∈ (univ : Finset ι) := mem_univ _
  have he : (fun t => product g (Function.update x i t)) =
      fun t => (∏ j ∈ univ.erase i, g j (x j)) * g i t := by
    funext t
    rw [product, ← prod_erase_mul _ (fun j => g j (Function.update x i t j)) hi,
      Function.update_self]
    congr 1
    apply prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [coordinateDeriv, he, deriv_const_mul_field, ← prod_erase_mul _ _ hi, ite_eq_left rfl]
  congr 1
  exact prod_congr rfl (fun j hj => (ite_eq_right (ne_of_mem_erase hj)).symm)

theorem mixedPartial_product (l : List ι) (g : ι → ℝ → ℝ) :
    mixedPartial l (product g) = product (fun i => iteratedDeriv (l.count i) (g i)) := by
  induction l with
  | nil => simp [mixedPartial]
  | cons i l ih =>
    funext x
    rw [mixedPartial, ih, partial_product, product]
    apply prod_congr rfl
    intro j _
    by_cases h : j = i
    · subst j
      simp [iteratedDeriv_succ]
    · simp [h, Ne.symm h]

theorem sum_count (l : List ι) : ∑ i : ι, l.count i = l.length := by
  simpa using (Multiset.sum_count_eq_card (m := (l : Multiset ι)) (s := univ)
    (fun a _ => mem_univ a))

theorem exists_list_of_multiIndex (α : ι → ℕ) :
    ∃ l : List ι, (∀ i, l.count i = α i) ∧ l.length = ∑ i, α i := by
  let m := Finsupp.toMultiset ((Finsupp.equivFunOnFinite : (ι →₀ ℕ) ≃ (ι → ℕ)).symm α)
  obtain ⟨l, hl⟩ := Quotient.exists_rep m
  have hc (i : ι) : l.count i = α i := by
    change (l : Multiset ι) = m at hl
    rw [← Multiset.coe_count, hl, ← Multiset.toFinsupp_apply]
    dsimp only [m]
    rw [Finsupp.toMultiset_toFinsupp]
    rfl
  exact ⟨l, hc, by simpa only [hc] using (sum_count l).symm⟩

theorem mixedPartial_bound {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 < ρ) (g : ι → ℝ → ℝ)
    (hg : ∀ (i : ι) (n : ℕ) x, ‖iteratedDeriv n (g i) x‖ ≤ ρ ^ n * (n.factorial : ℝ) ^ s)
    (l : List ι) (x : ι → ℝ) :
    ‖mixedPartial l (product g) x‖ ≤ ρ ^ l.length * (l.length.factorial : ℝ) ^ s := by
  have hcount := sum_count l
  have hfac : (∏ i : ι, ((l.count i).factorial : ℝ)) ≤ (l.length.factorial : ℝ) := by
    have hdvd := Nat.prod_factorial_dvd_factorial_sum (univ : Finset ι) (fun i => l.count i)
    rw [hcount] at hdvd
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  rw [mixedPartial_product, product, norm_prod]
  calc
    _ ≤ ∏ i : ι, ρ ^ l.count i * ((l.count i).factorial : ℝ) ^ s :=
      prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hg i _ _)
    _ = ρ ^ l.length * (∏ i : ι, ((l.count i).factorial : ℝ)) ^ s := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, hcount,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hfac hs) (by positivity)

omit [DecidableEq ι] in
theorem product_mem_Icc {g : ι → ℝ → ℝ} (hg : ∀ i t, g i t ∈ Set.Icc 0 1) (x : ι → ℝ) :
    product g x ∈ Set.Icc 0 1 := by
  refine ⟨prod_nonneg (fun i _ => (hg i _).1), ?_⟩
  simpa [product] using (prod_le_prod₀ (f := fun i : ι => g i (x i)) (g := fun _ => (1 : ℝ))
    (s := univ) (fun i _ => (hg i _).1) (fun i _ => (hg i _).2))

theorem exists_box_cutoff {s r R : ℝ} (hs : 1 < s) (hr : 0 < r) (hR : r < R) :
    ∃ b : (ι → ℝ) → ℝ, ∃ ρ : ℝ, 0 < ρ ∧ ContDiff ℝ (⊤ : ℕ∞) b ∧
      (∀ x, b x ∈ Set.Icc 0 1) ∧ (∀ x, (∀ i, |x i| ≤ r) → b x = 1) ∧
      tsupport b ⊆ Set.pi univ (fun _ => Ioo (-R) R) ∧ HasCompactSupport b ∧
      ∀ (l : List ι) x, ‖mixedPartial l b x‖ ≤ ρ ^ l.length * (l.length.factorial : ℝ) ^ s := by
  obtain ⟨f, ρ, hρ, hreg, h01, hplateau, hsupp, hcp, hbound⟩ := HeatGevreyCutoff.exists_cutoff hs hr hR
  let b : (ι → ℝ) → ℝ := product (fun _ => f)
  let K := Set.pi univ (fun _ : ι => tsupport f)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => hcp)
  have hsupport : tsupport b ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx i _
    apply subset_tsupport f
    intro hf
    apply hx
    exact prod_eq_zero (mem_univ i) hf
  refine ⟨b, ρ, hρ, contDiff_product _ (fun _ => hreg), product_mem_Icc (fun _ => h01),
    ?_, ?_, hK.of_isClosed_subset isClosed_closure hsupport,
    mixedPartial_bound (by linarith) hρ _ (fun _ => hbound)⟩
  · intro x hx
    simp [b, product, hplateau _ (hx _)]
  · exact hsupport.trans (Set.pi_mono fun _ _ => hsupp)

end HeatGevreyProduct

#print axioms HeatGevreyProduct.mixedPartial_product
#print axioms HeatGevreyProduct.exists_list_of_multiIndex
#print axioms HeatGevreyProduct.exists_box_cutoff
