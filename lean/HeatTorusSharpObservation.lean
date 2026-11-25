import HeatTorusObservation
import HeatTorusPaperDaviesGaffney

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace HeatTorusSharpObservation

open MeasureTheory Filter Set SHE SHE.PredictableL2 SHE.HilbertColumns
open HeatTorusReal UnitAddTorus HeatTorusCovarianceSeparation
open HeatTorusObservation (path)
open HeatTorusInitialData (rescale)
open HeatFlatTorusDistance (distance)
open HeatTorusPaperDaviesGaffney (setDistance setDistance_le)
open scoped NNReal ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

variable {ι : Type*} [Fintype ι]

theorem sharp_offDiagonal {P δ : ℝ} (hP : 0 < P) (O D : Set (UnitAddTorus ι))
    (hO : MeasurableSet O) (hδ : 0 < δ)
    (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ distance (rescale hP x) (rescale hP y)) :
    OffDiagonalBound P O D 1 (δ ^ 2 / 4) := by
  intro r L hL hr hrL f hf
  simpa only [one_mul] using
    HeatTorusPaperDaviesGaffney.supported_time_bound hP hδ hL hr hrL O D hO hsep f hf

/-- The physical distance dominates the period times the normalized product distance. -/
theorem mul_dist_le_distance {P : ℝ} (hP : 0 < P) (x y : UnitAddTorus ι) :
    P * dist x y ≤ distance (rescale hP x) (rescale hP y) := by
  obtain ⟨u, rfl⟩ := HeatFlatTorusSmoothLift.covering_surjective 1 x
  obtain ⟨v, rfl⟩ := HeatFlatTorusSmoothLift.covering_surjective 1 y
  let d := distance (rescale hP (HeatFlatTorusSmoothLift.covering 1 u))
    (rescale hP (HeatFlatTorusSmoothLift.covering 1 v))
  change P * dist (HeatFlatTorusSmoothLift.covering 1 u) (HeatFlatTorusSmoothLift.covering 1 v) ≤ d
  rw [mul_comm]
  apply (le_div_iff₀ hP).mp
  refine (dist_pi_le_iff (div_nonneg (norm_nonneg _) hP.le)).mpr (fun i => ?_)
  apply (le_div_iff₀ hP).mpr
  have h := PiLp.norm_apply_le (WithLp.toLp 2 (fun i =>
    dist (rescale hP (HeatFlatTorusSmoothLift.covering 1 u) i)
      (rescale hP (HeatFlatTorusSmoothLift.covering 1 v) i)) : EuclideanSpace ℝ ι) i
  change ‖dist (rescale hP (HeatFlatTorusSmoothLift.covering 1 u) i)
    (rescale hP (HeatFlatTorusSmoothLift.covering 1 v) i)‖ ≤ d at h
  rw [Real.norm_of_nonneg dist_nonneg] at h
  have hu := HeatTorusInitialData.rescale_coe hP (fun j => u j) i
  have hv := HeatTorusInitialData.rescale_coe hP (fun j => v j) i
  change rescale hP (HeatFlatTorusSmoothLift.covering 1 u) i = ((u i * P : ℝ) : AddCircle P) at hu
  change rescale hP (HeatFlatTorusSmoothLift.covering 1 v) i = ((v i * P : ℝ) : AddCircle P) at hv
  rw [hu, hv, dist_eq_norm, ← QuotientAddGroup.mk_sub, ← sub_mul, mul_comm (u i - v i) P] at h
  have hcancel : P⁻¹ * (P * (u i - v i)) = u i - v i := by
    rw [← mul_assoc, inv_mul_cancel₀ hP.ne', one_mul]
  rw [AddCircle.norm_eq' P hP, hcancel] at h
  change dist (u i : UnitAddCircle) (v i : UnitAddCircle) * P ≤ d
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq, mul_comm]
  exact h

theorem sharp_offDiagonal_of_separated {P δ : ℝ} (hP : 0 < P) (O D : Set (UnitAddTorus ι))
    (hO : MeasurableSet O) (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y) :
    OffDiagonalBound P O D 1 (gapConstant P δ) := by
  have h := sharp_offDiagonal hP O D hO (mul_pos hP hδ) fun x hx y hy =>
    (mul_le_mul_of_nonneg_left (hsep x hx y hy) hP.le).trans (mul_dist_le_distance hP x y)
  convert h using 1
  unfold gapConstant
  ring

/-- For nonempty sets, the exponent uses the actual physical set distance. -/
theorem exists_sharp_offDiagonal {P δ : ℝ} (hP : 0 < P) (O D : Set (UnitAddTorus ι))
    (hO : MeasurableSet O) (hδ : 0 < δ) (hsep : ∀ x ∈ O, ∀ y ∈ D, δ ≤ dist x y) :
    ∃ κ : ℝ, 0 < κ ∧ OffDiagonalBound P O D 1 κ ∧
      (O.Nonempty → D.Nonempty → κ = setDistance (rescale hP '' O) (rescale hP '' D) ^ 2 / 4) := by
  classical
  by_cases hn : O.Nonempty ∧ D.Nonempty
  · let A := rescale hP '' O
    let B := rescale hP '' D
    have hlower : P * δ ≤ setDistance A B := by
      apply le_csInf (((hn.1.image (rescale hP)).prod (hn.2.image (rescale hP))).image _)
      rintro _ ⟨⟨a, b⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
      exact (mul_le_mul_of_nonneg_left (hsep x hx y hy) hP.le).trans (mul_dist_le_distance hP x y)
    have hp : 0 < setDistance A B := (mul_pos hP hδ).trans_le hlower
    refine ⟨setDistance A B ^ 2 / 4, by positivity, sharp_offDiagonal hP O D hO hp ?_, fun _ _ => rfl⟩
    intro x hx y hy
    exact setDistance_le (mem_image_of_mem (rescale hP) hx) (mem_image_of_mem (rescale hP) hy)
  · refine ⟨gapConstant P δ, by unfold gapConstant; positivity,
      sharp_offDiagonal_of_separated hP O D hO hδ hsep, fun ho hd => (hn ⟨ho, hd⟩).elim⟩

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

theorem observation_cell_integral (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (hP : 0 < P) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    (hδ : 0 < setDistance (rescale hP '' O) (rescale hP '' D))
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (N : ℕ) (hN : 1 ≤ N)
    (htN : t N = T) (hstep : ∀ n, n < N → t n < t (n+1))
    (hnext : ∀ j, 1 ≤ j → j ≤ N → t (j+1) - t j ≤ t j - t (j-1))
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0) (n : ℕ) (hn : n < N) :
    (∫ s in Ioc (t n) (t (n+1)),
      (∫ ω, ‖observe O (path P M T W t N g s ω)‖^2 ∂μ) ∂timeMeasure T) ≤
      ‖g‖^2 * (Real.exp (-(setDistance (rescale hP '' O) (rescale hP '' D) ^ 2 / 4) / ((t (n+1)-t n:ℝ≥0):ℝ)) *
        (∏ k ∈ Finset.range n, (((t (k+1)-t k:ℝ≥0):ℝ))⁻¹)) *
        (1/2 + ((t (n+1):ℝ)-(t n:ℝ))/3) := by
  have hsep (x : UnitAddTorus ι) (hx : x ∈ O) (y : UnitAddTorus ι) (hy : y ∈ D) :=
    setDistance_le (mem_image_of_mem (rescale hP) hx) (mem_image_of_mem (rescale hP) hy)
  simpa only [one_mul] using
    HeatTorusObservation.observation_cell_integral_of_bound F μ T J hlocal W hW hWa hWc P M hM O D zero_le_one
      (sharp_offDiagonal hP O D hO hδ hsep) hMsupp t ht ht0 N hN htN hstep hnext g hg n hn

theorem exists_grid_bound (hT : 0 < T) (hlocal : StandardTerminalPastLocality J) (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ s, s ≤ T → (J.integral (StoppedItoInputs.stop F μ T s R) : Ω → ℝ) =ᵐ[μ] W s)
    (hWa : ∀ s, StronglyMeasurable[F s] (W s)) (hWc : ∀ ω, Continuous (fun s => W s ω))
    (P : ℝ) (hP : 0 < P) (M : RealState ι →L[ℝ] RealState ι) (hM : ‖M‖ ≤ 1)
    (O D : Set (UnitAddTorus ι)) (hO : MeasurableSet O)
    (hδ : 0 < setDistance (rescale hP '' O) (rescale hP '' D))
    (hMsupp : ∀ v : RealState ι, ∀ᵐ x ∂volume, x ∉ D → M v x = 0)
    (g : RealState ι) (hg : ∀ᵐ x ∂volume, x ∉ D → g x = 0) (L : ℝ) (hL : 1 ≤ L) :
    ∃ (t : ℕ → ℝ≥0) (N : ℕ), Monotone t ∧ t 0 = 0 ∧ 1 ≤ N ∧ t N = T ∧
      (∀ n, n < N → t n < t (n+1)) ∧
      (∫ p : ℝ≥0 × Ω, ‖observe O (path P M T W t N g p.1 p.2)‖^2 ∂energyMeasure μ T) ≤
        ‖g‖^2 * (2 * Real.exp (-(setDistance (rescale hP '' O) (rescale hP '' D) ^ 2 / 4) * L)) := by
  have hsep (x : UnitAddTorus ι) (hx : x ∈ O) (y : UnitAddTorus ι) (hy : y ∈ D) :=
    setDistance_le (mem_image_of_mem (rescale hP) hx) (mem_image_of_mem (rescale hP) hy)
  simpa only [one_mul] using
    HeatTorusObservation.exists_grid_bound_of_bound F μ T J hT hlocal W hW hWa hWc P M hM O D zero_le_one
      (by positivity : 0 < setDistance (rescale hP '' O) (rescale hP '' D) ^ 2 / 4)
      (sharp_offDiagonal hP O D hO hδ hsep) hMsupp g hg L hL

end HeatTorusSharpObservation

#print axioms HeatTorusSharpObservation.sharp_offDiagonal
#print axioms HeatTorusSharpObservation.sharp_offDiagonal_of_separated
#print axioms HeatTorusSharpObservation.exists_sharp_offDiagonal
#print axioms HeatTorusSharpObservation.observation_cell_integral
#print axioms HeatTorusSharpObservation.exists_grid_bound
