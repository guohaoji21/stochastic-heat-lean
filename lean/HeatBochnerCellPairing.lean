import HeatBochnerCell

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatBochnerCellPairing
open MeasureTheory Filter Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem pairing (f : ℝ≥0 × Ω → E) (hf : Measurable f)
    (hfm : MemLp f 2 (energyMeasure μ H)) (a b : ℝ≥0) (Y : Lp E 2 μ) :
    inner ℝ ((HeatBochnerCell.square_integrable μ H f hf hfm a b).toLp (HeatBochnerCell.value H f a b)) Y=
      ∫ p, (Ioc a b).indicator (fun s => inner ℝ (f (s,p.2)) (Y p.2)) p.1 ∂energyMeasure μ H := by
  have hym : MemLp (fun p : ℝ≥0 × Ω => Y p.2) 2 (energyMeasure μ H) :=
    (Lp.memLp Y).comp_snd (timeMeasure H)
  have hs : Integrable (fun p : ℝ≥0 × Ω => inner ℝ (f p) (Y p.2)) (energyMeasure μ H) := by
    apply (L2.integrable_inner (hfm.toLp f) (hym.toLp (fun p : ℝ≥0 × Ω => Y p.2))).congr
    filter_upwards [hfm.coeFn_toLp,hym.coeFn_toLp] with p hf hy
    change inner ℝ (hfm.toLp f p) (hym.toLp (fun q : ℝ≥0 × Ω => Y q.2) p)=inner ℝ (f p) (Y p.2)
    rw [hf,hy]
  have hi : Integrable (fun p : ℝ≥0 × Ω => (Ioc a b).indicator (fun s => inner ℝ (f (s,p.2)) (Y p.2)) p.1) (energyMeasure μ H) :=
    hs.indicator (measurableSet_Ioc.preimage measurable_fst)
  have hFub : (∫ p, (Ioc a b).indicator (fun s => inner ℝ (f (s,p.2)) (Y p.2)) p.1 ∂energyMeasure μ H)=
      ∫ ω,(∫ s in Ioc a b, inner ℝ (f (s,ω)) (Y ω) ∂timeMeasure H) ∂μ := by
    change (∫ p, (Ioc a b).indicator (fun s => inner ℝ (f (s,p.2)) (Y p.2)) p.1 ∂(timeMeasure H).prod μ)=_
    rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => integral_indicator measurableSet_Ioc)
  rw [L2.inner_def,hFub]
  apply integral_congr_ae
  filter_upwards [(HeatBochnerCell.square_integrable μ H f hf hfm a b).coeFn_toLp,
    HeatControlConvolution.time_memLp μ H f hf hfm] with ω hd hm
  rw [hd]
  have hInt : Integrable (fun s => f (s,ω)) ((timeMeasure H).restrict (Ioc a b)) :=
    (hm.integrable (by norm_num : (1:ENNReal)≤2)).integrableOn
  calc
    _ = inner ℝ (Y ω) (∫ s in Ioc a b,f (s,ω) ∂timeMeasure H) := real_inner_comm _ _
    _ = ∫ s in Ioc a b,inner ℝ (Y ω) (f (s,ω)) ∂timeMeasure H := (integral_inner hInt _).symm
    _ = _ := integral_congr_ae (Eventually.of_forall (fun s => real_inner_comm _ _))

end HeatBochnerCellPairing
#check @HeatBochnerCellPairing.pairing
#print HeatBochnerCellPairing.pairing
#print axioms HeatBochnerCellPairing.pairing
