import HeatWeightedIncrementMoments
import HeatBrownianProducts

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace HeatBrownianProductMoments
open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

theorem expectation (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s : ℝ≥0,s≤H → (J.integral (StoppedItoInputs.stop F μ H s R) : Ω → ℝ)=ᵐ[μ] W s)
    (hWa : ∀ s,StronglyMeasurable[F s] (W s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hT : ∀ n,n≤N → t n≤H) :
    ∀ n,n≤N → (∫ ω,HeatBrownianProducts.products W t n ω^2 ∂μ)=
      ∏ k∈Finset.range n,((t (k+1):ℝ)-(t k:ℝ))⁻¹ := by
  intro n
  induction n with
  | zero => intro _;simp [HeatBrownianProducts.products]
  | succ n ih =>
    intro hn
    have hp := HeatBrownianProducts.products_properties F μ H J hlocal W hW hWa t ht N hT n (by omega)
    have hs := HeatWeightedIncrementMoments.square F μ H J hlocal W hW
      (ht (Nat.le_succ n)) (hT (n+1) hn) (HeatBrownianProducts.products W t n) hp.1 hp.2
    let d : ℝ := (t (n+1):ℝ)-(t n:ℝ)
    have he : (∫ ω,HeatBrownianProducts.products W t (n+1) ω^2 ∂μ)=
        d⁻¹*(∫ ω,HeatBrownianProducts.products W t n ω^2 ∂μ) := by
      calc
        _ = (d⁻¹)^2*(∫ ω,(HeatBrownianProducts.products W t n ω*(W (t (n+1)) ω-W (t n) ω))^2 ∂μ) := by
          rw [←integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            dsimp only [d,HeatBrownianProducts.products]
            ring
        _ = (d⁻¹)^2*(d*(∫ ω,HeatBrownianProducts.products W t n ω^2 ∂μ)) :=
          congrArg (fun v : ℝ => (d⁻¹)^2*v) hs
        _ = _ := by
          by_cases hd : d=0
          · simp [hd]
          · field_simp
    rw [he,ih (by omega),Finset.prod_range_succ]
    dsimp [d]
    ring

end HeatBrownianProductMoments
#check @HeatBrownianProductMoments.expectation
#print HeatBrownianProductMoments.expectation
#print axioms HeatBrownianProductMoments.expectation
