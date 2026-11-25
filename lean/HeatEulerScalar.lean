import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatEulerScalar
open Filter
open scoped Topology

theorem inverse_bounds {c : ℝ} (hc : 0≤c) {k : ℕ} (hk : 0<k) :
    0≤(1+c/(k:ℝ))⁻¹ ∧ (1+c/(k:ℝ))⁻¹≤1 := by
  have hkn : (0:ℝ)<k := by exact_mod_cast hk
  have hd : 0≤c/(k:ℝ) := div_nonneg hc hkn.le
  constructor
  · positivity
  · apply (inv_le_one₀ (by positivity : (0:ℝ)<1+c/(k:ℝ))).mpr
    linarith

theorem tendsto_inverse (c : ℝ) :
    Tendsto (fun k : ℕ => ((1+c/(k:ℝ))⁻¹)^k) atTop (𝓝 (Real.exp (-c))) := by
  have he := (Real.tendsto_one_add_div_pow_exp c).inv₀ (ne_of_gt (Real.exp_pos c))
  simpa only [←inv_pow,←Real.exp_neg] using he

def count (T : ℝ) (n : ℕ) : ℕ := n+⌈T⌉₊+1

theorem count_positive (T : ℝ) (n : ℕ) : 0<count T n := by unfold count;omega

theorem count_ge (T : ℝ) (n : ℕ) : T≤(count T n:ℝ) := by
  apply (Nat.le_ceil T).trans
  exact_mod_cast (show ⌈T⌉₊≤count T n by unfold count;omega)

theorem count_tendsto (T : ℝ) : Tendsto (count T) atTop atTop := by
  exact tendsto_atTop_mono (fun n => by change n≤n+⌈T⌉₊+1;omega) tendsto_id

def parameter (T : ℝ) (n : ℕ) : ℝ := (count T n:ℝ)/T

theorem parameter_ge_one {T : ℝ} (hT : 0<T) (n : ℕ) : 1≤parameter T n := by
  apply (le_div_iff₀ hT).mpr
  simpa only [one_mul] using count_ge T n

theorem ratio {T c : ℝ} (hT : 0<T) (hc : 0≤c) (n : ℕ) :
    parameter T n/(parameter T n+c)=(1+(T*c)/(count T n:ℝ))⁻¹ := by
  have hk : (0:ℝ)<count T n := by exact_mod_cast count_positive T n
  have hd : parameter T n+c≠0 := ne_of_gt (add_pos_of_pos_of_nonneg (lt_of_lt_of_le zero_lt_one (parameter_ge_one hT n)) hc)
  have hd2 : 1+T*c/(count T n:ℝ)≠0 := ne_of_gt (by positivity)
  unfold parameter at *
  field_simp

end HeatEulerScalar
#check @HeatEulerScalar.inverse_bounds
#print axioms HeatEulerScalar.inverse_bounds
#check @HeatEulerScalar.tendsto_inverse
#print axioms HeatEulerScalar.tendsto_inverse
#check @HeatEulerScalar.count_positive
#print axioms HeatEulerScalar.count_positive
#check @HeatEulerScalar.count_ge
#print axioms HeatEulerScalar.count_ge
#check @HeatEulerScalar.count_tendsto
#print axioms HeatEulerScalar.count_tendsto
#check @HeatEulerScalar.parameter_ge_one
#print axioms HeatEulerScalar.parameter_ge_one
#check @HeatEulerScalar.ratio
#print HeatEulerScalar.ratio
#print axioms HeatEulerScalar.ratio
