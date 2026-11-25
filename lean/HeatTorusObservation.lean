import HeatTorusCovarianceSeparation
import HeatBackwardGlobalEnvelope
import HeatBackwardCellRestriction
import HeatNNObservationPolynomial
import HeatPathObservation
import HeatPartitionIntegral
import HeatPositiveGapPartition

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace HeatTorusObservation

open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open HeatTorusReal UnitAddTorus HeatTorusCovarianceSeparation
open scoped NNReal ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

local instance : MeasurableSpace (RealState ι) := borel _
local instance : BorelSpace (RealState ι) := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (RealState ι) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Space Unit ℝ) := borel _
local instance : BorelSpace (Space Unit ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (T : ℝ≥0) (J : StandardTerminalIto (C := Space Unit ℝ) (E := ℝ) F μ T)

local notation "R" => RawCylindricalCoordinates.row F μ T (HeatTerminalBrownian.e : Unit → Space Unit ℝ) ()

abbrev path (P : ℝ) (M : RealState ι →L[ℝ] RealState ι)
    (T : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) (g : RealState ι) :=
  HeatBackwardProcess.state (family P) (family_continuous P) (family_contraction P) M T W t N g

theorem observation_integrable (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) (O : Set (UnitAddTorus ι))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (N : ℕ) (hN : 1 ≤ N)
    (htN : t N = T) (hstep : ∀ n, n < N → t n < t (n+1)) (g : RealState ι) :
    Integrable (fun p : ℝ≥0 × Ω => ‖observe O (path P M T W t N g p.1 p.2)‖^2) (energyMeasure μ T) := by
  let X := path P M T W t N g
  have hS0 : family (ι := ι) P 0 = ContinuousLinearMap.id ℝ (RealState ι) := realHeat_zero P
  have hproducts := HeatBrownianProducts.products_properties F μ T J hlocal W hW hWa t ht N
    (fun n hn => (ht hn).trans htN.le)
  have hcont := HeatBackwardProcess.continuous_paths (family P) (family_continuous P)
    (family_contraction P) M hS0 W hWc t ht N hN hstep htN.le g
  have hpred := HeatBackwardProcess.predictable (family P) (family_continuous P)
    (family_contraction P) M F hS0 W hWc hWa t ht ht0 N hN hstep htN.le g
    (fun n hn => (hproducts n hn).1)
  have had := HeatBackwardProcess.adapted (family P) (family_continuous P)
    (family_contraction P) M F (H := T) W hWa t ht0 N hN g (fun n hn => (hproducts n hn).1)
  obtain ⟨D, hDm, hD0, hDb⟩ := HeatBackwardGlobalEnvelope.exists_envelope
    (family P) (family_continuous P) (family_contraction P) M F μ T J hlocal W hW hWa hWc
    t ht ht0 N hN htN.le g hproducts
  have hmax := HeatPathMaximum.integrable_square μ T X
    (fun a => (had a).measurable.mono (F.le a) le_rfl) hcont D hDm hD0 (by simpa only [htN] using hDb)
  exact HeatPathObservation.integrable μ T X hcont (hpred.mono (predictable_le_product F)) hmax (observe O)

theorem observation_cell_integral_of_bound (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) {C κ : ℝ} (hC : 0 ≤ C)
    (hbound : OffDiagonalBound P O D C κ)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (N : ℕ) (hN : 1 ≤ N)
    (htN : t N = T) (hstep : ∀ n, n < N → t n < t (n+1))
    (hnext : ∀ j, 1 ≤ j → j ≤ N → t (j+1) - t j ≤ t j - t (j-1))
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0) (n : ℕ) (hn : n < N) :
    (∫ s in Ioc (t n) (t (n+1)),
      (∫ ω, ‖observe O (path P M T W t N g s ω)‖^2 ∂μ) ∂timeMeasure T) ≤
      (C * ‖g‖)^2 * (Real.exp (-κ / ((t (n+1)-t n:ℝ≥0):ℝ)) *
        (∏ k ∈ Finset.range n, (((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) *
        (1/2 + ((t (n+1):ℝ)-(t n:ℝ))/3) := by
  let X := path P M T W t N g
  let A := (C * ‖g‖)^2
  let c (n : ℕ) := A * (Real.exp (-κ / ((t (n+1)-t n:ℝ≥0):ℝ)) *
    (∏ k ∈ Finset.range n, (((t (k+1)-t k:ℝ≥0):ℝ))⁻¹))
  let f := fun p : ℝ≥0 × Ω => ‖observe O (X p.1 p.2)‖^2
  let u := fun s => ∫ ω, f (s,ω) ∂μ
  have hi : Integrable f (energyMeasure μ T) :=
    observation_integrable F μ T J hlocal W hW hWa hWc P M O t ht ht0 N hN htN hstep g
  have hu : Integrable u (timeMeasure T) := hi.integral_prod_left
  have hT (n : ℕ) (hn : n ≤ N) : t n ≤ T := (ht hn).trans htN.le
  have hlen (k : ℕ) : ((t (k+1)-t k:ℝ≥0):ℝ) = (t (k+1):ℝ)-(t k:ℝ) :=
    NNReal.coe_sub (ht (Nat.le_succ k))
  have hbT := hT (n+1) (by omega)
  have hpoint (s : ℝ≥0) (hs : s ∈ Ioc (t n) (t (n+1))) :
      u s ≤ c n * HeatNNObservationPolynomial.weight (t n) (t (n+1)) s := by
    have hpath (ω : Ω) : X s ω = HeatBackwardNodes.cellState (family P) (family_continuous P)
        (family_contraction P) M T W t N g (n+1) s ω :=
      HeatBackwardCellRestriction.state_cell (family P) (family_continuous P) (family_contraction P)
        M W t ht N hN g (n+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) s
        (by simpa only [Nat.add_sub_cancel] using hs) ω
    have hpoint := observed_cell_bound_of_bound F μ T J hlocal W hW hWa P M hM O D hC hbound hMsupp
      t ht N hT g hg (n+1) (by omega) (by omega)
      (by simpa only [Nat.add_sub_cancel] using hstep n hn) (hnext (n+1) (by omega) (by omega)) s
      (by simpa only [Nat.add_sub_cancel] using hs.1.le) hs.2
    simp only [Nat.add_sub_cancel] at hpoint
    dsimp only [u, f, c, A, HeatNNObservationPolynomial.weight]
    simp_rw [hpath, hlen]
    convert hpoint using 1 <;> ring
  have hw := (HeatNNObservationPolynomial.integrable T (t n) (t (n+1))).const_mul (c n)
  calc
    _ ≤ ∫ s in Ioc (t n) (t (n+1)), c n * HeatNNObservationPolynomial.weight (t n) (t (n+1)) s
        ∂timeMeasure T := by
      apply integral_mono_ae hu.integrableOn hw
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using hpoint s hs
    _ = c n * (1/2 + ((t (n+1):ℝ)-(t n:ℝ))/3) := by
      rw [integral_const_mul, HeatNNObservationPolynomial.integral (hstep n hn) hbT]

theorem observation_sum_bound_of_bound (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) {C κ : ℝ} (hC : 0 ≤ C)
    (hbound : OffDiagonalBound P O D C κ)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (N : ℕ) (hN : 1 ≤ N)
    (htN : t N = T) (hstep : ∀ n, n < N → t n < t (n+1))
    (hnext : ∀ j, 1 ≤ j → j ≤ N → t (j+1) - t j ≤ t j - t (j-1))
    (hunit : ∀ n, n < N → t (n+1) - t n ≤ 1)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0) :
    (∫ p : ℝ≥0 × Ω, ‖observe O (path P M T W t N g p.1 p.2)‖^2 ∂energyMeasure μ T) ≤
      (C * ‖g‖)^2 *
        (∑ n ∈ Finset.range N, Real.exp (-κ / ((t (n+1)-t n:ℝ≥0):ℝ)) *
          (∏ k ∈ Finset.range n, (((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) := by
  let X := path P M T W t N g
  let A := (C * ‖g‖)^2
  let c (n : ℕ) := A * (Real.exp (-κ / ((t (n+1)-t n:ℝ≥0):ℝ)) *
    (∏ k ∈ Finset.range n, (((t (k+1)-t k:ℝ≥0):ℝ))⁻¹))
  let f := fun p : ℝ≥0 × Ω => ‖observe O (X p.1 p.2)‖^2
  let u := fun s => ∫ ω, f (s,ω) ∂μ
  have hi : Integrable f (energyMeasure μ T) :=
    observation_integrable F μ T J hlocal W hW hWa hWc P M O t ht ht0 N hN htN hstep g
  have hu : Integrable u (timeMeasure T) := hi.integral_prod_left
  have hlen (k : ℕ) : ((t (k+1)-t k:ℝ≥0):ℝ) = (t (k+1):ℝ)-(t k:ℝ) :=
    NNReal.coe_sub (ht (Nat.le_succ k))
  have hcell (n : ℕ) (hn : n ∈ Finset.range N) :
      (∫ s in Ioc (t n) (t (n+1)), u s ∂timeMeasure T) ≤ c n := by
    have hn' := Finset.mem_range.mp hn
    have hc : 0 ≤ c n := by dsimp only [c, A]; positivity
    have hcell := observation_cell_integral_of_bound F μ T J hlocal W hW hWa hWc P M hM
      O D hC hbound hMsupp t ht ht0 N hN htN hstep hnext g hg n hn'
    have hlen₁ : ((t (n+1)-t n:ℝ≥0):ℝ) ≤ 1 := by exact_mod_cast hunit n hn'
    rw [hlen] at hlen₁
    exact hcell.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (show 1/2 + ((t (n+1):ℝ)-(t n:ℝ))/3 ≤ 1 by linarith) hc)
  calc
    _ = ∫ s, u s ∂timeMeasure T := integral_prod _ hi
    _ = ∑ n ∈ Finset.range N, ∫ s in Ioc (t n) (t (n+1)), u s ∂timeMeasure T :=
      (HeatPartitionIntegral.whole _ hu t ht ht0 N htN).symm
    _ ≤ ∑ n ∈ Finset.range N, c n := Finset.sum_le_sum hcell
    _ = _ := (Finset.mul_sum ..).symm

theorem observation_sum_bound (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (hP : 0 < P) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (N : ℕ) (hN : 1 ≤ N)
    (htN : t N = T) (hstep : ∀ n, n < N → t n < t (n+1))
    (hnext : ∀ j, 1 ≤ j → j ≤ N → t (j+1) - t j ≤ t j - t (j-1))
    (hunit : ∀ n, n < N → t (n+1) - t n ≤ 1)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0) :
    (∫ p : ℝ≥0 × Ω, ‖observe O (path P M T W t N g p.1 p.2)‖^2 ∂energyMeasure μ T) ≤
      ((2 * (Fintype.card ι : ℝ)) * ‖g‖)^2 *
        (∑ n ∈ Finset.range N, Real.exp (-gapConstant P δ / ((t (n+1)-t n:ℝ≥0):ℝ)) *
          (∏ k ∈ Finset.range n, (((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) :=
  observation_sum_bound_of_bound F μ T J hlocal W hW hWa hWc P M hM O D (by positivity)
    (gaussian_offDiagonal P O D hP hO hδ hsep) hMsupp t ht ht0 N hN htN hstep hnext hunit g hg

/-- A sequence of increasingly fine grids produces actual periodic
adjoints with exponentially small total observation energy. -/
theorem exists_grid_bound_of_bound (hT : 0 < T) (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) {C κ : ℝ} (hC : 0 ≤ C)
    (hκ : 0 < κ) (hbound : OffDiagonalBound P O D C κ)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0) (L : ℝ) (hL : 1 ≤ L) :
    ∃ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t ∧ t 0 = 0 ∧ 1 ≤ N ∧ t N = T ∧
      (∀ n, n < N → t n < t (n+1)) ∧
      (∫ p : ℝ≥0 × Ω, ‖observe O (path P M T W t N g p.1 p.2)‖^2 ∂energyMeasure μ T) ≤
        (C * ‖g‖)^2 * (2 * Real.exp (-κ * L)) := by
  obtain ⟨N, hN, hbefore, hend⟩ := HeatPositiveGapPartition.exists_partition hκ hL T hT
  let d := HeatPositiveGapPartition.lengths hκ hL
  let t := HeatClippedPartition.nodes d T
  have ht := HeatClippedPartition.nodes_mono d T
  have hprops := HeatClippedPartition.nodes_properties d T (HeatPositiveGapPartition.lengths_positive hκ hL)
    hN hbefore hend
  have hnext (j : ℕ) (hj : 1 ≤ j) (_ : j ≤ N) : t (j+1) - t j ≤ t j - t (j-1) :=
    HeatClippedPartition.lengths_antitone d T (HeatPositiveGapPartition.lengths_antitone hκ hL)
      hN hbefore hend hj
  have hunit (n : ℕ) (hn : n < N) : t (n+1) - t n ≤ 1 := by
    have hb := HeatClippedPartition.length_bound d T hN hbefore hend (j := n+1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hb
    exact hb.trans (HeatPositiveGapPartition.lengths_le_one hκ hL n)
  refine ⟨t, N, ht, hprops.1, hN, hprops.2.1, hprops.2.2.1, ?_⟩
  exact (observation_sum_bound_of_bound F μ T J hlocal W hW hWa hWc P M hM O D hC hbound hMsupp
    t ht hprops.1 N hN hprops.2.1 hprops.2.2.1 hnext hunit g hg).trans
    (mul_le_mul_of_nonneg_left (HeatPositiveGapPartition.clipped_sum_bound hκ hL T hN hbefore hend) (sq_nonneg _))

theorem exists_grid_bound (hT : 0 < T) (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (hP : 0 < P) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y)
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0) (L : ℝ) (hL : 1 ≤ L) :
    ∃ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t ∧ t 0 = 0 ∧ 1 ≤ N ∧ t N = T ∧
      (∀ n, n < N → t n < t (n+1)) ∧
      (∫ p : ℝ≥0 × Ω, ‖observe O (path P M T W t N g p.1 p.2)‖^2 ∂energyMeasure μ T) ≤
        ((2 * (Fintype.card ι : ℝ)) * ‖g‖)^2 * (2 * Real.exp (-gapConstant P δ * L)) :=
  exists_grid_bound_of_bound F μ T J hT hlocal W hW hWa hWc P M hM O D (by positivity)
    (show 0 < gapConstant P δ by unfold gapConstant; positivity)
    (gaussian_offDiagonal P O D hP hO hδ hsep) hMsupp g hg L hL

end HeatTorusObservation

#print axioms HeatTorusObservation.observation_integrable
#print axioms HeatTorusObservation.observation_sum_bound
#print axioms HeatTorusObservation.exists_grid_bound

#print axioms HeatTorusObservation.observation_cell_integral_of_bound
#print axioms HeatTorusObservation.exists_grid_bound_of_bound
