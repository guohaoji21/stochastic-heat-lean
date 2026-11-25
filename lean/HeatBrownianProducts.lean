import HeatWeightedBrownian

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace HeatBrownianProducts
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ H)
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩
local notation "R" => RawCylindricalCoordinates.row F μ H (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

def products (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | n+1 => fun ω => products W t n ω * (W (t (n+1)) ω-W (t n) ω) / ((t (n+1):ℝ)-(t n:ℝ))

theorem products_properties (hlocal : StandardTerminalPastLocality J)
    (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t : ℝ≥0, t ≤ H → J.integral (StoppedItoInputs.stop F μ H t R) =ᵐ[μ] W t)
    (hWa : ∀ t, StronglyMeasurable[F t] (W t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (hT : ∀ n, n ≤ N → t n ≤ H) :
    ∀ n, n ≤ N → StronglyMeasurable[F (t n)] (products W t n) ∧ MemLp (products W t n) 2 μ := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨stronglyMeasurable_const,memLp_const 1⟩
  | succ n ih =>
    intro hn
    obtain ⟨ha,hm⟩ := ih (Nat.le_of_succ_le hn)
    have hstep : t n ≤ t (n+1) := ht (Nat.le_succ n)
    have hma := HeatWeightedBrownian.weighted_increment_memLp F μ H J hlocal W hW hstep (hT (n+1) hn)
      (products W t n) ha hm
    have haa := ha.mono (F.mono hstep)
    have hww := (hWa (t (n+1))).sub ((hWa (t n)).mono (F.mono hstep))
    constructor
    · change StronglyMeasurable[F (t (n+1))] (fun ω => products W t n ω * (W (t (n+1)) ω-W (t n) ω) / _)
      simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.sub_apply] using (haa.mul hww).mul_const (((t (n+1):ℝ)-(t n:ℝ))⁻¹)
    · simpa only [products,div_eq_mul_inv] using hma.mul_const (((t (n+1):ℝ)-(t n:ℝ))⁻¹)

theorem terminal_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (q : E)
    (hPa : StronglyMeasurable[F (t N)] (products W t N)) (hPm : MemLp (products W t N) 2 μ) :
    MemLp (fun ω => products W t N ω • q) 2 μ :=
  HeatWeightedCellInput.vector_memLp F μ (t N) (products W t N) hPa hPm q

end HeatBrownianProducts
#check @HeatBrownianProducts.products_properties
#print axioms HeatBrownianProducts.products_properties
#check @HeatBrownianProducts.terminal_memLp
#print axioms HeatBrownianProducts.terminal_memLp
