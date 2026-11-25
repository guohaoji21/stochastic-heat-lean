import HeatPastPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatMildCellPairing
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem lifted_self_adjoint (S : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (S x) y=inner ℝ x (S y)) (X Y : Lp E 2 μ) :
    inner ℝ ((S.compLpL 2 μ) X) Y=inner ℝ X ((S.compLpL 2 μ) Y) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [S.coeFn_compLpL X,S.coeFn_compLpL Y] with ω hx hy
  rw [hx,hy]
  exact hs _ _

theorem cell_identity (I : StandardTerminalIto (C := E) (E := E) F μ H)
    (hl : StandardTerminalPastLocality I) (a : ℝ≥0) (S : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (S x) y=inner ℝ x (S y))
    (Yₐ Yᵦ zₐ zᵦ U D : Lp E 2 μ)
    (hY : AEStronglyMeasurable[F a] Yₐ μ) (hz : AEStronglyMeasurable[F a] zₐ μ)
    (u v : Process (E := E) F μ H)
    (hy : Yᵦ=(S.compLpL 2 μ) Yₐ+U+I.integral (PastItoInputs.post F μ H a u))
    (hb : zₐ=(S.compLpL 2 μ) zᵦ+D-I.integral (PastItoInputs.post F μ H a v)) :
    inner ℝ Yᵦ ((S.compLpL 2 μ) zᵦ)-inner ℝ Yₐ ((S.compLpL 2 μ) zₐ)=
      inner ℝ U ((S.compLpL 2 μ) zᵦ)-inner ℝ ((S.compLpL 2 μ) Yₐ) D-
      inner ℝ (I.integral (PastItoInputs.post F μ H a u)) D+
      inner ℝ (PastItoInputs.post F μ H a u) (PastItoInputs.post F μ H a v) := by
  let A := S.compLpL 2 μ
  let N := I.integral (PastItoInputs.post F μ H a u)
  let M := I.integral (PastItoInputs.post F μ H a v)
  have hAY : AEStronglyMeasurable[F a] (A Yₐ) μ :=
    (S.continuous.comp_aestronglyMeasurable hY).congr (S.coeFn_compLpL Yₐ).symm
  have horth1 : inner ℝ (A Yₐ) M=0 := by
    have hh := HeatPastPairing.future_orthogonal I hl a v (A Yₐ) hAY
    exact (real_inner_comm _ _).trans hh
  have horth2 : inner ℝ N zₐ=0 := HeatPastPairing.future_orthogonal I hl a u zₐ hz
  have hcross : inner ℝ N M=inner ℝ (PastItoInputs.post F μ H a u) (PastItoInputs.post F μ H a v) :=
    I.integral.inner_map_map _ _
  have hsym := lifted_self_adjoint μ S hs Yₐ zₐ
  have hzb : A zᵦ=zₐ-D+M := by
    change zₐ=A zᵦ+D-M at hb
    rw [hb]
    abel
  change inner ℝ Yᵦ (A zᵦ)-inner ℝ Yₐ (A zₐ)=_
  rw [hy]
  change inner ℝ (A Yₐ+U+N) (A zᵦ)-inner ℝ Yₐ (A zₐ)=_
  simp only [inner_add_left]
  rw [hsym.symm,hzb]
  simp only [inner_add_right,inner_sub_right]
  linarith

end HeatMildCellPairing
#check @HeatMildCellPairing.lifted_self_adjoint
#print axioms HeatMildCellPairing.lifted_self_adjoint
#check @HeatMildCellPairing.cell_identity
#print HeatMildCellPairing.cell_identity
#print axioms HeatMildCellPairing.cell_identity
