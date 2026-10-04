import CoulombRotation_v1
import TwoElectronPartialProjection_v1
import NormalizedHydrogenGraph_v1

/-! Physical rotations fix the literal normalized hydrogen product. The tensor
covariance is proved for arbitrary L² factors using product measure. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
open TheoremT.Polar

theorem normalizedPolarGround_spatialRotation (Z : ℝ) (hZ : 0 < Z)
    (R : Position ≃ₗᵢ[ℝ] Position) :
    spatialRotation 1 R (normalizedPolarGround configuration_one_finrank Z hZ) =
      normalizedPolarGround configuration_one_finrank Z hZ := by
  unfold normalizedPolarGround
  rw [map_smul]
  congr 1
  apply Lp.ext
  have ht := (configurationRotation 1 R).measurePreserving.quasiMeasurePreserving.ae
    (polarGroundL2_coe configuration_one_finrank Z hZ)
  filter_upwards [configurationIsometryPull_ae (configurationRotation 1 R)
    (polarGroundL2 configuration_one_finrank Z hZ),ht,
    polarGroundL2_coe configuration_one_finrank Z hZ] with x hx ht hx'
  simp only [Function.comp_apply] at hx
  rw [hx,ht,hx']
  simp only [polarGroundFunction,LinearIsometryEquiv.norm_map]

theorem twoElectronConfigurationProduct_rotation_fst
    (R : Position ≃ₗᵢ[ℝ] Position) (x : Configuration 2) :
    (twoElectronConfigurationProduct (configurationRotation 2 R x)).1 =
      configurationRotation 1 R (twoElectronConfigurationProduct x).1 := by
  ext ⟨i,k⟩
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

theorem twoElectronConfigurationProduct_rotation_snd
    (R : Position ≃ₗᵢ[ℝ] Position) (x : Configuration 2) :
    (twoElectronConfigurationProduct (configurationRotation 2 R x)).2 =
      configurationRotation 1 R (twoElectronConfigurationProduct x).2 := by
  ext ⟨i,k⟩
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

theorem twoElectronTensor_spatialRotation (R : Position ≃ₗᵢ[ℝ] Position)
    (f g : SpatialL2 1) :
    spatialRotation 2 R (twoElectronTensor f g) =
      twoElectronTensor (spatialRotation 1 R f) (spatialRotation 1 R g) := by
  apply Lp.ext
  have hp1 := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Configuration 1))) (ν := (volume : Measure (Configuration 1)))).ae
      (configurationIsometryPull_ae (configurationRotation 1 R) f)
  have hp2 := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Configuration 1))) (ν := (volume : Measure (Configuration 1)))).ae
      (configurationIsometryPull_ae (configurationRotation 1 R) g)
  have h1 := twoElectronConfigurationProduct_measurePreserving.quasiMeasurePreserving.ae hp1
  have h2 := twoElectronConfigurationProduct_measurePreserving.quasiMeasurePreserving.ae hp2
  have ht := (configurationRotation 2 R).measurePreserving.quasiMeasurePreserving.ae
    (twoElectronTensor_ae f g)
  filter_upwards [configurationIsometryPull_ae (configurationRotation 2 R)
    (twoElectronTensor f g),ht,twoElectronTensor_ae (spatialRotation 1 R f)
      (spatialRotation 1 R g),h1,h2] with x hx ht hs h1 h2
  simp only [Function.comp_apply] at *
  rw [hx,ht,hs,h1,h2,twoElectronConfigurationProduct_rotation_fst,
    twoElectronConfigurationProduct_rotation_snd]

theorem hydrogenProduct_spatialRotation (Z : ℝ) (hZ : 0 < Z)
    (R : Position ≃ₗᵢ[ℝ] Position) :
    spatialRotation 2 R
      (twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hZ)
        (normalizedPolarGround configuration_one_finrank Z hZ)) =
      twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hZ)
        (normalizedPolarGround configuration_one_finrank Z hZ) := by
  rw [twoElectronTensor_spatialRotation,normalizedPolarGround_spatialRotation]

#print axioms twoElectronTensor_spatialRotation
#print axioms hydrogenProduct_spatialRotation
end TheoremT.Continuum
