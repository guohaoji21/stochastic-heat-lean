import HeatResolventSpectrum
import HeatFourierFrameConvergence
import HeatEulerScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace HeatDirichletEuler
open MeasureTheory Filter HeatIntervalNormalization HeatWeakDirichlet HeatDirichletResolvent HeatFourierFrame
open HeatEulerScalar
open scoped Topology

def value (T : ℝ) (hT : 0<T) (n : ℕ) (f : Base) : Base :=
  ((smoothing (parameter T n) (parameter_ge_one hT n) : Base → Base)^[count T n]) f

theorem coordinate_value (T : ℝ) (hT : 0<T) (n : ℕ) (f : Base) (k : ℤ) :
    coordinate k (value T hT n f)=((1+(T*rate k)/(count T n:ℝ))⁻¹)^(count T n)*coordinate k f := by
  rw [value,HeatResolventSpectrum.coordinate_iterate,ratio hT (rate_nonnegative k)]

theorem coordinate_tendsto (T : ℝ) (hT : 0<T) (f : Base) (k : ℤ) :
    Tendsto (fun n => coordinate k (value T hT n f)) atTop (𝓝 (coordinate k (paperHeat T f))) := by
  simp_rw [coordinate_value]
  rw [HeatResolventSpectrum.coordinate_heat T hT.le]
  have he := ((tendsto_inverse (T*rate k)).comp (count_tendsto T)).mul_const (coordinate k f)
  simpa only [Function.comp_def,neg_mul] using he

theorem coordinate_bound (T : ℝ) (hT : 0<T) (n : ℕ) (f : Base) (k : ℤ) :
    |coordinate k (value T hT n f)|≤|coordinate k f| := by
  rw [coordinate_value,abs_mul]
  obtain ⟨h0,h1⟩ := inverse_bounds (mul_nonneg hT.le (rate_nonnegative k)) (count_positive T n)
  have hp : 0≤((1+(T*rate k)/(count T n:ℝ))⁻¹)^(count T n) := pow_nonneg h0 _
  rw [abs_of_nonneg hp]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ h0 h1)

theorem heat_coordinate_bound (T : ℝ) (hT : 0≤T) (f : Base) (k : ℤ) :
    |coordinate k (paperHeat T f)|≤|coordinate k f| := by
  rw [HeatResolventSpectrum.coordinate_heat T hT,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_of_le_one_left (abs_nonneg _)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hT) (rate_nonnegative k))

theorem tendsto_heat (T : ℝ) (hT : 0<T) (f : Base) :
    Tendsto (fun n => value T hT n f) atTop (𝓝 (paperHeat T f)) := by
  apply HeatFourierFrameConvergence.tendsto _ _ f (coordinate_tendsto T hT f)
  intro n k
  rw [map_sub]
  exact (abs_sub _ _).trans (by linarith [coordinate_bound T hT n f k,heat_coordinate_bound T hT.le f k])

theorem nonnegative (T : ℝ) (hT : 0≤T) (f : Base) (hf : ∀ᵐ x ∂baseMeasure,0≤f x) :
    ∀ᵐ x ∂baseMeasure,0≤paperHeat T f x := by
  rcases eq_or_lt_of_le hT with hz | hp
  · rw [←hz,paperHeat_zero]
    exact hf
  · apply HeatFourierFrameConvergence.nonnegative_limit _ _ (tendsto_heat T hp f)
    intro n
    exact HeatResolventSpectrum.iterate_nonnegative (parameter_ge_one hp n) f hf (count T n)

end HeatDirichletEuler
#check @HeatDirichletEuler.coordinate_value
#print axioms HeatDirichletEuler.coordinate_value
#check @HeatDirichletEuler.coordinate_tendsto
#print axioms HeatDirichletEuler.coordinate_tendsto
#check @HeatDirichletEuler.coordinate_bound
#print axioms HeatDirichletEuler.coordinate_bound
#check @HeatDirichletEuler.heat_coordinate_bound
#print axioms HeatDirichletEuler.heat_coordinate_bound
#check @HeatDirichletEuler.tendsto_heat
#print axioms HeatDirichletEuler.tendsto_heat
#check @HeatDirichletEuler.nonnegative
#print HeatDirichletEuler.nonnegative
#print axioms HeatDirichletEuler.nonnegative
