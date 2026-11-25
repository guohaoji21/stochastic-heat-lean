import HeatBackwardDriftKernel

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatBackwardGluing
open MeasureTheory Filter Set
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (μ : Measure Ω) (S : ℝ≥0 → E →L[ℝ] E)
  (D I : ℝ≥0 → ℝ≥0 → Ω → E) (z : ℝ≥0 → Ω → E)

def Equation (a b : ℝ≥0) : Prop :=
  z a =ᵐ[μ] (fun ω => S (b-a) (z b ω)+D a b ω-I a b ω)

theorem trans (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b)
    (hD : D a b =ᵐ[μ] fun ω => D a c ω+S (c-a) (D c b ω))
    (hI : I a b =ᵐ[μ] fun ω => I a c ω+S (c-a) (I c b ω))
    (hacEq : Equation μ S D I z a c) (hcbEq : Equation μ S D I z c b) :
    Equation μ S D I z a b := by
  filter_upwards [hD,hI,hacEq,hcbEq] with ω hd hi ha hc
  rw [ha,hc,map_sub,map_add,hd,hi]
  have ht : (c-a)+(b-c)=b-a := by rw [add_comm]; exact tsub_add_tsub_cancel hcb hac
  have hs := congrArg (fun A : E →L[ℝ] E => A (z b ω)) (hsem (c-a) (b-c))
  rw [ht] at hs
  change S (b-a) (z b ω) = S (c-a) (S (b-c) (z b ω)) at hs
  rw [hs]
  abel

theorem on_grid (hsem : ∀ s t, S (s+t) = (S s).comp (S t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ)
    (hD : ∀ a c b, a≤c → c≤b → D a b =ᵐ[μ] fun ω => D a c ω+S (c-a) (D c b ω))
    (hI : ∀ a c b, a≤c → c≤b → I a b =ᵐ[μ] fun ω => I a c ω+S (c-a) (I c b ω))
    (hself : Equation μ S D I z (t N) (t N))
    (hcell : ∀ j, 1≤j → j≤N → Equation μ S D I z (t (j-1)) (t j)) :
    ∀ j, j≤N → Equation μ S D I z (t j) (t N) := by
  intro j hj
  apply Nat.decreasingInduction (motive := fun j _ => Equation μ S D I z (t j) (t N)) ?_ hself hj
  intro k hk ih
  have hkN : k<N := Nat.lt_of_succ_le hk
  apply trans μ S D I z hsem (ht (Nat.le_succ k)) (ht hk)
    (hD _ _ _ (ht (Nat.le_succ k)) (ht hk)) (hI _ _ _ (ht (Nat.le_succ k)) (ht hk)) _ ih
  simpa only [Nat.add_sub_cancel] using hcell (k+1) (by omega) hk

theorem exists_cell (t : ℕ → ℝ≥0) (ht : Monotone t) :
    ∀ N, 1≤N → ∀ a, t 0≤a → a≤t N → ∃ j, 1≤j ∧ j≤N ∧ t (j-1)≤a ∧ a≤t j := by
  intro N
  induction N with
  | zero => omega
  | succ n ih =>
    intro hN a ha hb
    by_cases hn : n=0
    · subst n
      exact ⟨1,le_rfl,le_rfl,ha,hb⟩
    · by_cases hh : a≤t n
      · obtain ⟨j,hj,hjn,hlo,hhi⟩ := ih (by omega) a ha hh
        exact ⟨j,hj,by omega,hlo,hhi⟩
      · exact ⟨n+1,by omega,le_rfl,by simpa only [Nat.add_sub_cancel] using (le_of_not_ge hh),hb⟩

end HeatBackwardGluing
#check @HeatBackwardGluing.trans
#print axioms HeatBackwardGluing.trans
#check @HeatBackwardGluing.on_grid
#print axioms HeatBackwardGluing.on_grid
#check @HeatBackwardGluing.exists_cell
#print axioms HeatBackwardGluing.exists_cell
