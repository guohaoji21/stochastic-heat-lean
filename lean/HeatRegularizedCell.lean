import HeatMildCellPairing

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatRegularizedCell
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem identity (A B C : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y=inner ℝ x (A y))
    (hB : ∀ x y, inner ℝ (B x) y=inner ℝ x (B y))
    (hC : ∀ x y, inner ℝ (C x) y=inner ℝ x (C y))
    (hAB : A.comp B=B.comp A) (hBC : B=C.comp A)
    (Ya Yb za zb U D N M : E)
    (hy : Yb=A Ya+U+N) (hz : za=A zb+D-M)
    (horth1 : inner ℝ (B Ya) M=0) (horth2 : inner ℝ (C N) za=0) :
    inner ℝ Yb (B zb)-inner ℝ Ya (B za)=
      inner ℝ U (B zb)-inner ℝ (B Ya) D-inner ℝ (C N) D+inner ℝ (C N) M := by
  have hcomm (x : E) : A (B x)=B (A x) := congrArg (fun L : E →L[ℝ] E => L x) hAB
  have hN : inner ℝ N (B zb)=inner ℝ (C N) (A zb) := by
    rw [hBC]
    exact (hC N (A zb)).symm
  have hdet : inner ℝ (A Ya) (B zb)=inner ℝ (B Ya) (A zb) := by
    rw [hA,hcomm]
    exact (hB Ya (A zb)).symm
  have hzb : A zb=za-D+M := by rw [hz];abel
  rw [hy]
  simp only [inner_add_left]
  rw [hN,hdet,hzb,←hB Ya za]
  simp only [inner_add_right,inner_sub_right]
  linarith

end HeatRegularizedCell
#check @HeatRegularizedCell.identity
#print HeatRegularizedCell.identity
#print axioms HeatRegularizedCell.identity
