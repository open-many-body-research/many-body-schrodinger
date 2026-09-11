import TwoElectronPartialProjection_v1
import ProductL2PartialIntegralRight_v1

/-! Literal partial-integral formulas in the actual two-electron coordinates.
Equalities are almost everywhere, as required for L2 representatives. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectronContractFirst_ae_integral (f : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronContractFirst f F =ᵐ[volume] fun y =>
      ∫ x, inner ℂ (f x) (F (twoElectronConfigurationProduct.symm (x,y))) := by
  have hrep := twoElectronL2ToProduct_ae F
  have hs := (Measure.measurePreserving_swap
    (μ := (volume : Measure (Configuration 1))) (ν := volume)).quasiMeasurePreserving.ae hrep
  filter_upwards [ProductL2.contractLeft_ae_partialIntegral f (twoElectronL2ProductEquiv F),
    Measure.ae_ae_of_ae_prod hs] with y hy hslice
  change ProductL2.contractLeft f (twoElectronL2ProductEquiv F) y = _
  rw [hy]
  apply integral_congr_ae
  filter_upwards [hslice] with x hx
  change twoElectronL2ProductEquiv F (x,y) =
    F (twoElectronConfigurationProduct.symm (x,y)) at hx
  rw [hx]

theorem twoElectronContractSecond_ae_integral (g : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronContractSecond g F =ᵐ[volume] fun x =>
      ∫ y, inner ℂ (g y) (F (twoElectronConfigurationProduct.symm (x,y))) := by
  filter_upwards [ProductL2.contractRight_ae_partialIntegral g (twoElectronL2ProductEquiv F),
    Measure.ae_ae_of_ae_prod (twoElectronL2ToProduct_ae F)] with x hx hslice
  change ProductL2.contractRight g (twoElectronL2ProductEquiv F) x = _
  rw [hx]
  apply integral_congr_ae
  filter_upwards [hslice] with y hy
  change twoElectronL2ProductEquiv F (x,y) =
    F (twoElectronConfigurationProduct.symm (x,y)) at hy
  rw [hy]

theorem twoElectronProjectFirst_ae_integral (f : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronProjectFirst f F =ᵐ[volume] fun q =>
      f (twoElectronConfigurationProduct q).1 *
        ∫ x, inner ℂ (f x)
          (F (twoElectronConfigurationProduct.symm (x,(twoElectronConfigurationProduct q).2))) := by
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Configuration 1))) (ν := volume)).ae
      (twoElectronContractFirst_ae_integral f F)
  have hq := twoElectronConfigurationProduct_measurePreserving.quasiMeasurePreserving.ae hp
  rw [twoElectronProjectFirst_apply]
  filter_upwards [twoElectronTensor_ae f (twoElectronContractFirst f F),hq] with q ht hq
  rw [ht,hq]

theorem twoElectronProjectSecond_ae_integral (g : SpatialL2 1) (F : SpatialL2 2) :
    twoElectronProjectSecond g F =ᵐ[volume] fun q =>
      (∫ y, inner ℂ (g y)
        (F (twoElectronConfigurationProduct.symm ((twoElectronConfigurationProduct q).1,y)))) *
        g (twoElectronConfigurationProduct q).2 := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Configuration 1))) (ν := (volume : Measure (Configuration 1)))).ae
      (twoElectronContractSecond_ae_integral g F)
  have hq := twoElectronConfigurationProduct_measurePreserving.quasiMeasurePreserving.ae hp
  rw [twoElectronProjectSecond_apply]
  filter_upwards [twoElectronTensor_ae (twoElectronContractSecond g F) g,hq] with q ht hq
  rw [ht,hq]

#print axioms twoElectronContractFirst_ae_integral
#print axioms twoElectronContractSecond_ae_integral
#print axioms twoElectronProjectFirst_ae_integral
#print axioms twoElectronProjectSecond_ae_integral
end TheoremT.Continuum
