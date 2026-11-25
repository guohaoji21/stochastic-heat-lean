import HeatPredictableDriftCell
import HeatPastPairing
import HeatTerminalItoCompression

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace HeatBackwardDriver

open Filter MeasureTheory SHE SHE.PredictableL2 SHE.PastItoInputs SHE.StoppedItoInputs
open scoped NNReal ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {F : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

private abbrev projection (F : Filtration ℝ≥0 mΩ) (t : ℝ≥0) (X : Lp E 2 μ) : Lp E 2 μ :=
  (condExpL2 E ℝ (F.le t) X : Lp E 2 μ)

def mean (X : Lp E 2 μ) : Lp E 2 μ := Lp.const 2 μ (∫ ω, X ω ∂μ)

private theorem mean_adapted (t : ℝ≥0) (X : Lp E 2 μ) :
    AEStronglyMeasurable[F t] (mean X : Ω → E) μ :=
  stronglyMeasurable_const.aestronglyMeasurable.congr (Lp.coeFn_const ..).symm

private theorem centered (X : Lp E 2 μ) : (∫ ω, (X - mean X) ω ∂μ) = 0 := by
  have he : (X - mean X : Lp E 2 μ) =ᵐ[μ] fun ω => X ω - ∫ z, X z ∂μ := by
    filter_upwards [Lp.coeFn_sub X (mean X), Lp.coeFn_const 2 μ (∫ z, X z ∂μ)] with ω h₁ h₂
    exact h₁.trans (congrArg (X ω - ·) h₂)
  rw [integral_congr_ae he, integral_sub ((Lp.memLp X).integrable one_le_two) (integrable_const _),
    integral_const]
  simp

private theorem projection_adapted (t : ℝ≥0) (X : Lp E 2 μ) :
    AEStronglyMeasurable[F t] (projection F t X : Ω → E) μ :=
  aestronglyMeasurable_condExpL2 (𝕜 := ℝ) (F.le t) X

private theorem projection_eq (t : ℝ≥0) (X : Lp E 2 μ)
    (hX : AEStronglyMeasurable[F t] (X : Ω → E) μ) : projection F t X = X := by
  apply Lp.ext
  simpa only [Lp.toLp_coeFn] using ((Lp.memLp X).condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le t)).trans
    (condExp_of_aestronglyMeasurable' (F.le t) hX ((Lp.memLp X).integrable one_le_two))

private theorem projection_sub (t : ℝ≥0) (X Y : Lp E 2 μ) :
    projection F t (X - Y) = projection F t X - projection F t Y := by
  change ((condExpL2 E ℝ (F.le t) (X - Y)) : Lp E 2 μ) = _
  rw [map_sub]
  rfl

private theorem projection_residual_norm (t : ℝ≥0) (X : Lp E 2 μ) :
    ‖X - projection F t X‖ ≤ ‖X‖ := by
  letI : Fact (F t ≤ mΩ) := ⟨F.le t⟩
  let K := lpMeas E ℝ (F t) 2 μ
  change ‖X - K.starProjection X‖ ≤ ‖X‖
  rw [← K.starProjection_orthogonal_val]
  exact Kᗮ.norm_starProjection_apply_le X

variable (J : StandardTerminalIto (C := E) (E := E) F μ H)

private theorem past_adapted (t : ℝ≥0) (u : Process (E := E) F μ H) :
    AEStronglyMeasurable[F t] (J.integral (stop F μ H t u) : Ω → E) μ := by
  obtain ⟨g, hg, he⟩ := J.adapted t (stop F μ H t u) (stop_stopped F μ H t u)
  exact hg.aestronglyMeasurable.congr he.symm

private theorem post_eq_sub_stop {t : ℝ≥0} (ht : t ≤ H) (u : Process (E := E) F μ H) :
    post F μ H t u = u - stop F μ H t u := by
  simpa only [SHEStochastic.FiniteItoStoppedVersions.stop_horizon] using
    PastItoAlgebra.post_stop_eq_sub F μ H t H ht u

private theorem projection_of_martingale (hJ : StandardTerminalPastLocality J)
    {t : ℝ≥0} (ht : t ≤ H) (X : Lp E 2 μ) (u : Process (E := E) F μ H)
    (hu : J.integral u = X - mean X) :
    projection F t X = mean X + J.integral (stop F μ H t u) := by
  let Y := mean X + J.integral (stop F μ H t u)
  have hY : AEStronglyMeasurable[F t] (Y : Ω → E) μ := by
    exact ((mean_adapted t X).add (past_adapted J t u)).congr (Lp.coeFn_add _ _).symm
  have hx : X = Y + J.integral (post F μ H t u) := by
    dsimp only [Y]
    rw [post_eq_sub_stop ht, map_sub, hu]
    abel
  have hX : (X : Ω → E) =ᵐ[μ] fun ω => Y ω +
      (J.integral (stop F μ H H u) ω - J.integral (stop F μ H t u) ω) := by
    rw [SHEStochastic.FiniteItoStoppedVersions.stop_horizon, hx]
    have hp : J.integral (post F μ H t u) =
        J.integral u - J.integral (stop F μ H t u) := by rw [post_eq_sub_stop ht, map_sub]
    filter_upwards [Lp.coeFn_add Y (J.integral (post F μ H t u)),
      Lp.coeFn_sub (J.integral u) (J.integral (stop F μ H t u))] with ω he hd
    rw [he, Pi.add_apply, hp]
    exact congrArg (Y ω + ·) hd
  apply Lp.ext
  simpa only [Lp.toLp_coeFn] using ((Lp.memLp X).condExpL2_ae_eq_condExp (𝕜 := ℝ) (F.le t)).trans
    (HeatHilbertFutureCenter.conditional_mean_of_mild_decomposition J hJ ht u Y X
      ((Lp.memLp Y).integrable one_le_two) hY hX)

/-- The conditional L² state for a prescribed predictable drift and terminal value. -/
def state (b : ℝ≥0) (η : Lp E 2 μ) (f : Process (E := E) F μ H) (t : ℝ≥0) : Lp E 2 μ :=
  projection F t (η + HeatPredictableDriftCell.value t b f)

theorem state_adapted (b : ℝ≥0) (η : Lp E 2 μ) (f : Process (E := E) F μ H) (t : ℝ≥0) :
    AEStronglyMeasurable[F t] (state b η f t : Ω → E) μ :=
  projection_adapted t _

theorem state_terminal (b : ℝ≥0) (η : Lp E 2 μ)
    (hη : AEStronglyMeasurable[F b] (η : Ω → E) μ) (f : Process (E := E) F μ H) :
    state b η f b = η := by
  rw [state, HeatPredictableDriftCell.self, add_zero]
  exact projection_eq b η hη

theorem state_norm_sq_sub_le {t b : ℝ≥0} (ht : t ≤ b) (hb : b ≤ H)
    (η : Lp E 2 μ) (f g : Process (E := E) F μ H) :
    ‖state b η f t - state b η g t‖ ^ 2 ≤ ((b : ℝ) - t) * ‖f - g‖ ^ 2 := by
  unfold state
  rw [← projection_sub, add_sub_add_left_eq_sub, ← HeatPredictableDriftCell.sub]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_condExpL2_coe_le (𝕜 := ℝ) (F.le t) _) 2).trans
    (HeatPredictableDriftCell.norm_sq_le ht hb _)

/-- The terminal value with the full prescribed drift included. -/
def terminal (a b : ℝ≥0) (η : Lp E 2 μ) (f : Process (E := E) F μ H) : Lp E 2 μ :=
  η + HeatPredictableDriftCell.value a b f

theorem terminal_adapted {a b : ℝ≥0} (η : Lp E 2 μ)
    (hη : AEStronglyMeasurable[F b] (η : Ω → E) μ) (f : Process (E := E) F μ H) :
    AEStronglyMeasurable[F b] (terminal a b η f : Ω → E) μ :=
  (hη.add (HeatPredictableDriftCell.adapted a b f)).congr (Lp.coeFn_add _ _).symm

/-- The martingale representing the modified terminal value is stopped at its
own endpoint, even when constructed using the original longer horizon. -/
theorem exists_noise (hJ : StandardTerminalPastLocality J)
    (hrep : ∀ X : Lp E 2 μ, AEStronglyMeasurable[F H] (X : Ω → E) μ →
      (∫ ω, X ω ∂μ) = 0 → ∃ u : Process (E := E) F μ H, J.integral u = X)
    {a b : ℝ≥0} (hb : b ≤ H) (η : Lp E 2 μ)
    (hη : AEStronglyMeasurable[F b] (η : Ω → E) μ) (f : Process (E := E) F μ H) :
    ∃ u : Process (E := E) F μ H,
      J.integral u = terminal a b η f - mean (terminal a b η f) ∧ stop F μ H b u = u := by
  let X := terminal a b η f
  have hX : AEStronglyMeasurable[F b] (X - mean X : Lp E 2 μ) μ :=
    ((terminal_adapted η hη f).sub (mean_adapted b X)).congr (Lp.coeFn_sub _ _).symm
  obtain ⟨u, hu⟩ := hrep (X - mean X) (hX.mono (F.mono hb)) (centered X)
  have he := HeatTerminalItoCompression.integral_eq_stopped_of_measurable J hJ hb u (by rwa [hu])
  exact ⟨u, hu, J.integral.injective he.symm⟩

/-- The adapted state is the stopped martingale minus the accumulated drift. -/
theorem state_eq_stopped (hJ : StandardTerminalPastLocality J)
    {a t b : ℝ≥0} (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ H)
    (η : Lp E 2 μ) (f u : Process (E := E) F μ H)
    (hu : J.integral u = terminal a b η f - mean (terminal a b η f)) :
    state b η f t =
      mean (terminal a b η f) + J.integral (stop F μ H t u) - HeatPredictableDriftCell.value a t f := by
  let X := terminal a b η f
  have hsplit : η + HeatPredictableDriftCell.value t b f = X - HeatPredictableDriftCell.value a t f := by
    dsimp only [X, terminal]
    rw [HeatPredictableDriftCell.split hat htb f]
    abel
  unfold state
  rw [hsplit, projection_sub, projection_eq t _ (HeatPredictableDriftCell.adapted a t f),
    projection_of_martingale J hJ (htb.trans hb) X u hu]

/-- The prescribed-driver backward identity at every deterministic point of a cell. -/
theorem equation (hJ : StandardTerminalPastLocality J)
    {a t b : ℝ≥0} (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ H)
    (η : Lp E 2 μ) (f u : Process (E := E) F μ H)
    (hu : J.integral u = terminal a b η f - mean (terminal a b η f)) :
    state b η f t =
      η + HeatPredictableDriftCell.value t b f - J.integral (post F μ H t u) := by
  rw [state_eq_stopped J hJ hat htb hb η f u hu, post_eq_sub_stop (htb.trans hb), map_sub, hu,
    terminal, HeatPredictableDriftCell.split hat htb f]
  abel

/-- The post-initial-time noise of the prescribed solution is Lipschitz in the drift
with squared constant equal to the length of the cell. -/
theorem noise_norm_sq_sub_le (hJ : StandardTerminalPastLocality J)
    {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ H)
    (η : Lp E 2 μ) (f g u v : Process (E := E) F μ H)
    (hu : J.integral u = terminal a b η f - mean (terminal a b η f))
    (hv : J.integral v = terminal a b η g - mean (terminal a b η g)) :
    ‖post F μ H a u - post F μ H a v‖ ^ 2 ≤ ((b : ℝ) - a) * ‖f - g‖ ^ 2 := by
  let X := terminal a b η f
  let Y := terminal a b η g
  have hfuture (z : Lp E 2 μ) (w : Process (E := E) F μ H)
      (hw : J.integral w = z - mean z) :
      J.integral (post F μ H a w) = z - projection F a z := by
    rw [projection_of_martingale J hJ (hab.trans hb) z w hw, post_eq_sub_stop (hab.trans hb), map_sub, hw]
    abel
  rw [← J.integral.norm_map (post F μ H a u - post F μ H a v), map_sub,
    hfuture X u hu, hfuture Y v hv]
  have he : X - projection F a X - (Y - projection F a Y) =
      (X - Y) - projection F a (X - Y) := by
    rw [projection_sub]
    abel
  rw [he]
  have hXY : X - Y = HeatPredictableDriftCell.value a b (f - g) := by
    dsimp only [X, Y, terminal]
    rw [add_sub_add_left_eq_sub, HeatPredictableDriftCell.sub]
  refine (pow_le_pow_left₀ (norm_nonneg _) (projection_residual_norm a (X - Y)) 2).trans ?_
  rw [hXY]
  exact HeatPredictableDriftCell.norm_sq_le hab hb (f - g)

end HeatBackwardDriver

#print axioms HeatBackwardDriver.exists_noise
#print axioms HeatBackwardDriver.equation
#print axioms HeatBackwardDriver.state_norm_sq_sub_le
#print axioms HeatBackwardDriver.noise_norm_sq_sub_le
