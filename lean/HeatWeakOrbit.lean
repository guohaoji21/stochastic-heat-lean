import HeatDirichletIdentification
import HeatIntervalCovariance
import HeatConcreteSemigroupInput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace HeatWeakOrbit
open MeasureTheory HeatIntervalNormalization HeatWeakDirichlet
open HeatPhysicalGenerator
open scoped NNReal

theorem orbit_integral (f g : Base) (hfg : weakLaplacian f g) (t : ℝ) (ht : 0≤t) :
    paperHeat t f-f=∫ s in (0:ℝ)..t,paperHeat s g := by
  apply measureEquiv.injective
  have hc := HeatDirichletIdentification.weak_fourier_identity f g hfg
  have hn := HeatGeneratorSufficient.orbit_integral (measureEquiv f) (measureEquiv g) hc t ht
  let L := measureEquiv.toLinearIsometry.toContinuousLinearMap
  have hi := L.intervalIntegral_comp_comm (μ := volume) ((paperHeat_continuous g).intervalIntegrable 0 t)
  change L (paperHeat t f-f)=L (∫ s in (0:ℝ)..t,paperHeat s g)
  rw [map_sub,←hi]
  simpa only [L,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry,
    measureEquiv_heat] using hn

theorem time_integral (f g : Base) (hfg : weakLaplacian f g) (t : ℝ≥0) :
    HeatConcreteSemigroupInput.family t f-f=∫ s,HeatConcreteSemigroupInput.family s g ∂SHE.PredictableL2.timeMeasure t := by
  have hi := HeatIntervalCovariance.interval_integral 0 t (fun s => HeatConcreteSemigroupInput.family s g)
  have ht : (SHE.PredictableL2.timeMeasure t)=SHE.PredictableL2.intervalTimeMeasure 0 t := by
    simp only [SHE.PredictableL2.timeMeasure,SHE.PredictableL2.intervalTimeMeasure,NNReal.coe_zero]
  rw [ht,hi]
  simp only [NNReal.coe_zero]
  change paperHeat (t:ℝ) f-f=∫ s in Set.Ioc (0:ℝ) (t:ℝ),paperHeat (s.toNNReal:ℝ) g
  calc
    _ = ∫ s in (0:ℝ)..(t:ℝ),paperHeat s g := orbit_integral f g hfg (t:ℝ) t.property
    _ = ∫ s in Set.Ioc (0:ℝ) (t:ℝ),paperHeat s g := intervalIntegral.integral_of_le t.property
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.coe_toNNReal s hs.1.le]

end HeatWeakOrbit
#check @HeatWeakOrbit.orbit_integral
#print axioms HeatWeakOrbit.orbit_integral
#check @HeatWeakOrbit.time_integral
#print HeatWeakOrbit.time_integral
#print axioms HeatWeakOrbit.time_integral
