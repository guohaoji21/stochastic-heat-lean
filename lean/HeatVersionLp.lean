import HeatVolterraSlice
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace HeatVersionLp
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω E T : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace T] [FirstCountableTopology T]
  (μ : Measure Ω) [IsFiniteMeasure μ]
  (X : T → Ω → E) (hm : ∀ t, StronglyMeasurable (X t))
  (D : Ω → ℝ) (hD : MemLp D 2 μ) (hD0 : ∀ ω, 0≤D ω)
  (hb : ∀ t ω, ‖X t ω‖≤D ω)

def mem (t : T) : MemLp (X t) 2 μ :=
  hD.mono' (hm t).aestronglyMeasurable (Filter.Eventually.of_forall (hb t))

def value (t : T) : Lp E 2 μ := (mem μ X hm D hD hb t).toLp (X t)

theorem value_ae (t : T) : value μ X hm D hD hb t=ᵐ[μ] X t :=
  (mem μ X hm D hD hb t).coeFn_toLp

include hD0 in
theorem continuous [Nontrivial E] (hc : ∀ ω, Continuous (fun t => X t ω)) :
    Continuous (value μ X hm D hD hb) := by
  obtain ⟨v,hv⟩ := exists_norm_eq E (by norm_num : (0:ℝ)≤1)
  have hdm : MemLp (fun ω => D ω • v) 2 μ := by
    apply (hD.norm.const_mul ‖v‖).mono' (hD.aestronglyMeasurable.smul_const v)
    exact Filter.Eventually.of_forall (fun ω => by rw [norm_smul];exact le_of_eq (mul_comm _ _))
  let dom : Lp E 2 μ := hdm.toLp (fun ω => D ω • v)
  have hdom : ∀ᵐ ω ∂μ, ‖dom ω‖=D ω := by
    filter_upwards [hdm.coeFn_toLp] with ω hω
    rw [hω,norm_smul,hv,mul_one,Real.norm_eq_abs,abs_of_nonneg (hD0 ω)]
  apply continuous_iff_seqContinuous.mpr
  intro s t ht
  apply HeatVolterraSlice.dominated_Lp_convergence μ
    (fun n => value μ X hm D hD hb (s n)) (value μ X hm D hD hb t) dom
  · intro n
    filter_upwards [value_ae μ X hm D hD hb (s n),hdom] with ω hx hd
    rw [hx,hd]
    exact hb _ _
  · filter_upwards [ae_all_iff.mpr (fun n => value_ae μ X hm D hD hb (s n)),
      value_ae μ X hm D hD hb t] with ω hs htv
    change Tendsto (fun n => value μ X hm D hD hb (s n) ω) atTop (𝓝 (value μ X hm D hD hb t ω))
    rw [htv]
    have he : (fun n => value μ X hm D hD hb (s n) ω)=(fun n => X (s n) ω) := funext hs
    rw [he]
    exact (hc ω).continuousAt.tendsto.comp ht

end HeatVersionLp
#check @HeatVersionLp.value_ae
#print axioms HeatVersionLp.value_ae
#check @HeatVersionLp.continuous
#print axioms HeatVersionLp.continuous
