import HydrogenProductTrialEnergy_v1
import HydrogenRadialNorm_v1
import OneElectronEuclidean_v1
import CoulombTwoElectronExpectation_v1

/-!
Actual normalized hydrogen product density and coordinate integral transport.
The tensor and physical repulsion are the existing continuum definitions.
No moment, pushforward, normalization constant or integrability is assumed.
-/
noncomputable section
open MeasureTheory Filter
open TheoremT.Continuum TheoremT.Polar TheoremT.HydrogenPolynomial

namespace ManyBody.S2

/-- Assemble two genuine Euclidean electron positions in the existing configuration. -/
def hydrogenProductEuclideanCoordinates :
    (AngularR3 × AngularR3) ≃L[ℝ] Configuration 2 :=
  (oneElectronEuclidean.symm.toContinuousLinearEquiv.prodCongr
    oneElectronEuclidean.symm.toContinuousLinearEquiv).trans
    twoElectronConfigurationProduct.symm

theorem hydrogenProductEuclideanCoordinates_measurePreserving :
    MeasurePreserving hydrogenProductEuclideanCoordinates
      ((volume : Measure AngularR3).prod volume) volume :=
  twoElectronConfigurationProduct_symm_measurePreserving.comp
    (oneElectronEuclidean.symm.measurePreserving.prod
      oneElectronEuclidean.symm.measurePreserving)

@[simp] theorem hydrogenProductEuclideanCoordinates_first (p : AngularR3 × AngularR3) :
    position (hydrogenProductEuclideanCoordinates p) (0 : Fin 2) = p.1 := by
  ext k
  simp [hydrogenProductEuclideanCoordinates, position,
    oneElectronEuclidean_symm_apply]

@[simp] theorem hydrogenProductEuclideanCoordinates_second (p : AngularR3 × AngularR3) :
    position (hydrogenProductEuclideanCoordinates p) (1 : Fin 2) = p.2 := by
  ext k
  simp [hydrogenProductEuclideanCoordinates, position,
    oneElectronEuclidean_symm_apply]

/-- The density of the actual normalized physical orbital, with exact π normalization. -/
theorem normalizedHydrogen_density_ae (α : ℝ) (hα : 0 < α) :
    ∀ᵐ x : Configuration 1 ∂volume,
      ‖normalizedPolarGround configuration_one_finrank α hα x‖ ^ 2 =
        (α ^ 3 / Real.pi) * Real.exp (-(2 * α) * ‖x‖) := by
  have hn := hydrogenRadialL2_norm_sq α hα
  have he := Lp.coeFn_smul (‖hydrogenRadialL2 α hα‖⁻¹ : ℂ)
    (hydrogenRadialL2 α hα)
  simp only [normalizedPolarGround, polarGroundL2_eq_hydrogen]
  filter_upwards [he, hydrogenRadialL2_coe_ae α hα] with x hx hy
  rw [hx]
  simp only [Pi.smul_apply]
  rw [hy, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_pow, inv_pow, hn]
  simp only [hydrogenRadial, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  rw [inv_div]
  congr 1
  congr 1
  ring

theorem hydrogenProduct_tensor_density_ae (α : ℝ) (hα : 0 < α) :
    ∀ᵐ p : AngularR3 × AngularR3 ∂((volume : Measure AngularR3).prod volume),
      ‖twoElectronTensor (normalizedPolarGround configuration_one_finrank α hα)
        (normalizedPolarGround configuration_one_finrank α hα)
        (hydrogenProductEuclideanCoordinates p)‖ ^ 2 =
      (α ^ 6 / Real.pi ^ 2) *
        (Real.exp (-(2 * α) * ‖p.1‖) * Real.exp (-(2 * α) * ‖p.2‖)) := by
  have he := hydrogenProductEuclideanCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (twoElectronTensor_ae (normalizedPolarGround configuration_one_finrank α hα)
      (normalizedPolarGround configuration_one_finrank α hα))
  have hd := oneElectronEuclidean.symm.measurePreserving.quasiMeasurePreserving.ae
    (normalizedHydrogen_density_ae α hα)
  have hdf := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure AngularR3)) (ν := (volume : Measure AngularR3))).ae hd
  have hds := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure AngularR3)) (ν := (volume : Measure AngularR3))).ae hd
  filter_upwards [he, hdf, hds] with p hp hpx hpy
  simp only [hydrogenProductEuclideanCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,
    twoElectronConfigurationProduct.apply_symm_apply] at hp ⊢
  rw [hp, norm_mul, mul_pow]
  change ‖normalizedPolarGround configuration_one_finrank α hα (oneElectronEuclidean.symm p.1)‖ ^ 2 *
    ‖normalizedPolarGround configuration_one_finrank α hα (oneElectronEuclidean.symm p.2)‖ ^ 2 = _
  rw [hpx, hpy]
  simp only [LinearIsometryEquiv.norm_map]
  ring

theorem hydrogenProductRepulsion_weighted_density_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun p : AngularR3 × AngularR3 =>
      (α ^ 6 / Real.pi ^ 2) *
        (Real.exp (-(2 * α) * ‖p.1‖) * Real.exp (-(2 * α) * ‖p.2‖)) /
        ‖p.1 - p.2‖) ((volume : Measure AngularR3).prod volume) := by
  let f := normalizedPolarGround configuration_one_finrank α hα
  have hi := pair_potential_energy_integrable_of_weakH1 (0 : Fin 2) 1 (by decide)
    (twoElectronTensor f f) (twoElectronTensorGradient f f
      (normalizedHydrogenGradient α hα) (normalizedHydrogenGradient α hα))
    (twoElectronTensorGradient_weak f f _ _
      (normalizedHydrogenGradient_weak α hα) (normalizedHydrogenGradient_weak α hα))
  have hit := hydrogenProductEuclideanCoordinates_measurePreserving.integrable_comp_of_integrable hi
  apply hit.congr
  filter_upwards [hydrogenProduct_tensor_density_ae α hα] with p hp
  change ‖twoElectronTensor f f (hydrogenProductEuclideanCoordinates p)‖ ^ 2 /
    ‖position (hydrogenProductEuclideanCoordinates p) (0 : Fin 2) -
      position (hydrogenProductEuclideanCoordinates p) (1 : Fin 2)‖ = _
  rw [hydrogenProductEuclideanCoordinates_first, hydrogenProductEuclideanCoordinates_second, hp]

/-- Genuine product integrability, inherited from the physical weak-H1 tensor. -/
theorem hydrogenProductRepulsion_density_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun p : AngularR3 × AngularR3 =>
      Real.exp (-(2 * α) * ‖p.1‖) * Real.exp (-(2 * α) * ‖p.2‖) /
        ‖p.1 - p.2‖) ((volume : Measure AngularR3).prod volume) := by
  have hi := (hydrogenProductRepulsion_weighted_density_integrable α hα).const_mul
    (Real.pi ^ 2 / α ^ 6)
  convert hi using 1
  funext p
  field_simp [hα.ne', Real.pi_ne_zero]

/-- The physical repulsion is the literal Euclidean exponential double integral. -/
theorem hydrogenProductRepulsion_eq_double_integral (α : ℝ) (hα : 0 < α) :
    hydrogenProductRepulsion α hα =
      (α ^ 6 / Real.pi ^ 2) *
        ∫ y : AngularR3, ∫ x : AngularR3,
          Real.exp (-(2 * α) * ‖x‖) * Real.exp (-(2 * α) * ‖y‖) / ‖x - y‖ := by
  calc
    _ = ∫ p : AngularR3 × AngularR3,
        ‖twoElectronTensor (normalizedPolarGround configuration_one_finrank α hα)
          (normalizedPolarGround configuration_one_finrank α hα)
          (hydrogenProductEuclideanCoordinates p)‖ ^ 2 /
          ‖position (hydrogenProductEuclideanCoordinates p) 0 -
            position (hydrogenProductEuclideanCoordinates p) 1‖
          ∂((volume : Measure AngularR3).prod volume) :=
      (hydrogenProductEuclideanCoordinates_measurePreserving.integral_comp
        hydrogenProductEuclideanCoordinates.toHomeomorph.measurableEmbedding
        (fun q => ‖twoElectronTensor
          (normalizedPolarGround configuration_one_finrank α hα)
          (normalizedPolarGround configuration_one_finrank α hα) q‖ ^ 2 /
          ‖position q 0 - position q 1‖)).symm
    _ = ∫ p : AngularR3 × AngularR3,
        (α ^ 6 / Real.pi ^ 2) *
          (Real.exp (-(2 * α) * ‖p.1‖) * Real.exp (-(2 * α) * ‖p.2‖)) /
            ‖p.1 - p.2‖ ∂((volume : Measure AngularR3).prod volume) := by
      apply integral_congr_ae
      filter_upwards [hydrogenProduct_tensor_density_ae α hα] with p hp
      rw [hydrogenProductEuclideanCoordinates_first,
        hydrogenProductEuclideanCoordinates_second, hp]
    _ = (α ^ 6 / Real.pi ^ 2) *
        ∫ p : AngularR3 × AngularR3,
          Real.exp (-(2 * α) * ‖p.1‖) * Real.exp (-(2 * α) * ‖p.2‖) / ‖p.1 - p.2‖
          ∂((volume : Measure AngularR3).prod volume) := by
      rw [← integral_const_mul]
      congr 1
      funext p
      ring
    _ = _ := by
      rw [integral_prod_symm _ (hydrogenProductRepulsion_density_integrable α hα)]

/-- The actual inner Newton integral is integrable for almost every physical center. -/
theorem hydrogenRepulsion_inner_integrable_ae (α : ℝ) (hα : 0 < α) :
    ∀ᵐ y : AngularR3 ∂volume,
      Integrable (fun x : AngularR3 =>
        Real.exp (-(2 * α) * ‖x‖) / ‖x - y‖) volume := by
  filter_upwards [(hydrogenProductRepulsion_density_integrable α hα).prod_left_ae] with y hy
  have hi := hy.const_mul (Real.exp (-(2 * α) * ‖y‖))⁻¹
  convert hi using 1
  funext x
  field_simp [(Real.exp_pos (-(2 * α) * ‖y‖)).ne']

#print axioms normalizedHydrogen_density_ae
#print axioms hydrogenProduct_tensor_density_ae
#print axioms hydrogenProductRepulsion_density_integrable
#print axioms hydrogenProductRepulsion_eq_double_integral
#print axioms hydrogenRepulsion_inner_integrable_ae
end ManyBody.S2
